import SszArm.BoolStoreExec
import SszArm.BoolAlignment

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem StoreOp.effect_program (op : StoreOp) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [StoreOp.effect, state_simp_rules]

theorem StoreOp.effect_error (op : StoreOp) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [StoreOp.effect, state_simp_rules]

theorem StoreOp.effect_pc (op : StoreOp) (s : ArmState) :
    read_pc (op.effect s) = read_pc s + 4#64 := by
  cases op <;> simp [StoreOp.effect, state_simp_rules]

theorem StoreOp.effect_aligned (op : StoreOp) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  cases op <;> simp [StoreOp.effect, state_simp_rules, ha]
  all_goals first
    | exact aligned_sub16 _ (stack_aligned s ha)
    | exact aligned_sub32 _ (stack_aligned s ha)
    | exact aligned_add16 _ (stack_aligned s ha)
    | exact aligned_add32 _ (stack_aligned s ha)

theorem StoreOp.effect_reg (op : StoreOp) (s : ArmState) (reg : BitVec 5)
    (hr : reg ∉ [8#5, 9#5, 10#5, 11#5, 31#5]) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  cases op <;>
    simp (disch := first | decide | simp_all) [StoreOp.effect, state_simp_rules]

def storeBlock (ops : List StoreOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

theorem storeBlock_reg (ops : List StoreOp) (s : ArmState) (reg : BitVec 5)
    (hr : reg ∉ [8#5, 9#5, 10#5, 11#5, 31#5]) :
    r (.GPR reg) (storeBlock ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih (op.effect s)).trans (op.effect_reg s reg hr)

theorem storeBlock_program (ops : List StoreOp) (s : ArmState) :
    (storeBlock ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih (op.effect s)).trans (op.effect_program s)

theorem storeBlock_error (ops : List StoreOp) (s : ArmState) :
    read_err (storeBlock ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih (op.effect s)).trans (op.effect_error s)

theorem storeBlock_aligned (ops : List StoreOp) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (storeBlock ops s) := by
  induction ops generalizing s with
  | nil => exact ha
  | cons op ops ih => exact ih (op.effect s) (op.effect_aligned s ha)

theorem storeBlock_pc (ops : List StoreOp) (s : ArmState) :
    read_pc (storeBlock ops s) = read_pc s + BitVec.ofNat 64 (4 * ops.length) := by
  induction ops generalizing s with
  | nil => simp [storeBlock]
  | cons op ops ih =>
    change read_pc (storeBlock ops (op.effect s)) = _
    rw [ih, StoreOp.effect_pc]
    simp only [List.length_cons, Nat.mul_succ, BitVec.ofNat_add]
    bv_omega

theorem storeBlock_run (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (start : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 start)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hwords : ∀ i : Fin ops.length,
      (start + 4 * i.val, (ops[i]).word) ∈ program) :
    run ops.length s = storeBlock ops s := by
  induction ops generalizing s start with
  | nil => rfl
  | cons op ops ih =>
    have hw : (start, op.word) ∈ program := by
      simpa using hwords ⟨0, by simp⟩
    have hf : s.program.find? (read_pc s) = some op.word := by
      simpa only [hp] using hc (start, op.word) hw
    change run (ops.length + 1) s = storeBlock ops (op.effect s)
    rw [run, step_word s op he ha hf]
    apply ih (op.effect s) (start + 4)
    · simpa only [CodeAt, StoreOp.effect_program] using hc
    · simp [StoreOp.effect_pc, hp, BitVec.ofNat_add, BitVec.add_assoc]
    · simpa only [StoreOp.effect_error] using he
    · exact StoreOp.effect_aligned op s ha
    · intro i
      have hw := hwords ⟨i.val + 1, by simpa using i.isLt⟩
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw

def zeroPair (offset : StoreOp) : List StoreOp :=
  [.subSp16, .strX9Sp, .strX10Sp8, .addX9X0_0, offset,
   .movX10_0, .strX10X9, .movX10_0, .strX10X9_8,
   .ldrX10Sp8, .ldrX9Sp, .addSp16]

def trueStores : List StoreOp :=
  [.movW8_256, .subSp32, .strX9Sp, .strX10Sp8, .strX11Sp16,
   .addX9X0_0, .addX9X9_16, .lsrW11W8_8, .strbW8X9, .strbW11X9_1,
   .ldrX11Sp16, .ldrX10Sp8, .ldrX9Sp, .addSp32]

def falseStores : List StoreOp :=
  [.subSp32, .strX9Sp, .strX10Sp8, .strX11Sp16, .addX9X0_0, .addX9X9_16,
   .movW10_0, .lsrW11W10_8, .strbW10X9, .strbW11X9_1,
   .ldrX11Sp16, .ldrX10Sp8, .ldrX9Sp, .addSp32]

def scopeStores : List StoreOp :=
  [.movW8_1, .movW9_3] ++ zeroPair .addX9X9_56 ++ zeroPair .addX9X9_16 ++
  [.subSp16, .strX9Sp, .strX10Sp8, .addX9X0_0, .addX9X9_32,
   .strX8X9, .movX10_0, .strX10X9_8, .ldrX10Sp8, .ldrX9Sp, .addSp16,
   .strX3X0_48, .strW9X0_72, .stpX8X8X0]

def badStores : List StoreOp :=
  zeroPair .addX9X9_56 ++ zeroPair .addX9X9_40 ++ zeroPair .addX9X9_16 ++
  [.strX8X0_32, .movW8_13]

def tagStores : List StoreOp :=
  [.subSp16, .strX9Sp, .strX10Sp8, .addX9X0_0, .movX10_0,
   .strX10X9, .ldrX10Sp8, .ldrX9Sp, .addSp16]

theorem true_stores_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 628#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 14 s = storeBlock trueStores s :=
  storeBlock_run trueStores s base 628 hc hp he ha (by decide)

theorem false_stores_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4084#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 14 s = storeBlock falseStores s :=
  storeBlock_run falseStores s base 4084 hc hp he ha (by decide)

theorem scope_stores_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 2084#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 40 s = storeBlock scopeStores s :=
  storeBlock_run scopeStores s base 2084 hc hp he ha (by decide)

theorem bad_stores_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4144#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 38 s = storeBlock badStores s :=
  storeBlock_run badStores s base 4144 hc hp he ha (by decide)

theorem tag_stores_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4504#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 9 s = storeBlock tagStores s :=
  storeBlock_run tagStores s base 4504 hc hp he ha (by decide)

theorem stores_sp (s : ArmState) (ops : List StoreOp)
    (h : ops ∈ [trueStores, falseStores, scopeStores, badStores, tagStores]) :
    r (.GPR 31#5) (storeBlock ops s) = r (.GPR 31#5) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true, instances := true})
      [storeBlock, trueStores, falseStores, scopeStores, badStores, tagStores,
       zeroPair, StoreOp.effect, state_simp_rules]
    bv_omega

end SszArm.BoolCodec
