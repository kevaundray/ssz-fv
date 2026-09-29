import SszArm.CodecEmitPartsOps

namespace SszArm.Codec.Emit.Parts

open SszArm.Emit.Activation (next put save)
open SszArm.Emit.ReturnBlock (restore)
open Delimited (MemoryFrame)

def bodySP (s : ArmState) : BitVec 64 := r (.GPR 31#5) s - 224#64

def prologueOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p20, .p24]

@[irreducible] def prologue (s : ArmState) : ArmState := block prologueOps s

def savedRegisters : List (BitVec 5 × Nat) :=
  [(29#5, 128), (30#5, 136), (28#5, 144), (27#5, 152),
   (26#5, 160), (25#5, 168), (24#5, 176), (23#5, 184),
   (22#5, 192), (21#5, 200), (20#5, 208), (19#5, 216)]

/-- Six physical paired stores made before any child is visited. -/
def savedMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 208#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
  (write_mem_bytes 16 (bodySP s + 192#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
  (write_mem_bytes 16 (bodySP s + 176#64) (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
  (write_mem_bytes 16 (bodySP s + 160#64) (r (.GPR 25#5) s ++ r (.GPR 26#5) s)
  (write_mem_bytes 16 (bodySP s + 144#64) (r (.GPR 27#5) s ++ r (.GPR 28#5) s)
  (write_mem_bytes 16 (bodySP s + 128#64) (r (.GPR 30#5) s ++ r (.GPR 29#5) s) s)))))

@[simp] theorem prologue_sp (s : ArmState) :
    r (.GPR 31#5) (prologue s) = bodySP s := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, bodySP, state_simp_rules]

@[simp] theorem prologue_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 31#5) :
    r (.GPR reg) (prologue s) = r (.GPR reg) s := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, different, state_simp_rules]

@[simp] theorem prologue_pc (s : ArmState) : read_pc (prologue s) = read_pc s + 28#64 := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (s : ArmState) : (prologue s).program = s.program := by
  simp [prologue]

@[simp] theorem prologue_error (s : ArmState) : read_err (prologue s) = read_err s := by
  simp [prologue]

@[simp] theorem prologue_memory (s : ArmState) : (prologue s).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save,
    savedMemory, bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem prologue_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (prologue s) = r (.SFP reg) s := by
  simp [prologue]

theorem bodySP_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    Aligned (bodySP s) 4 := by
  simp (config := {decide := true}) [CheckSPAlignment, read_gpr, bodySP,
    Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
  bv_omega

theorem prologue_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (prologue s) :=
  CheckSPAlignment_of_r_sp_aligned (prologue_sp s) (bodySP_aligned s aligned)

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run 7 s = prologue s := by
  have afterSP := bodySP_aligned s aligned
  have follows : Follows base prologueOps s := by
    change r .PC s = base at pc
    simp (config := {decide := true}) [Follows, prologueOps, Op.row, Op.effect,
      put, next, save, state_simp_rules, CheckSPAlignment, read_gpr,
      BitVec.setWidth_eq, bodySP, pc, BitVec.add_assoc] at aligned afterSP ⊢
    exact ⟨aligned, afterSP⟩
  rw [prologue]
  exact runs prologueOps s base code error follows

theorem prologue_frame (s : ArmState) (low : 224 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 96, 96)] s (prologue s) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 96, 96) (by simp)
  simp only [Prod.fst, Prod.snd] at apart
  rw [prologue_memory]
  simp only [savedMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address
    (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)]

theorem prologue_saved (s : ArmState) (low : 224 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (prologue s) = r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (prologue_memory s))]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [savedMemory]
    simp (disch := (simp only [bodySP]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

def restoreOps : List Op :=
  [.p1088, .p1092, .p1096, .p1100, .p1104, .p1108, .p1112, .p1116]

@[irreducible] def restored (s : ArmState) : ArmState := block restoreOps s

@[simp] theorem restored_program (s : ArmState) : (restored s).program = s.program := by
  simp [restored]

@[simp] theorem restored_error (s : ArmState) : read_err (restored s) = read_err s := by
  simp [restored]

@[simp] theorem restored_memory (s : ArmState) : (restored s).mem = s.mem := by
  simp [restored, restoreOps, block, Op.effect, restore, put, next, state_simp_rules]

@[simp] theorem restored_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (restored s) = r (.SFP reg) s := by
  simp [restored]

theorem restored_run (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1088#64) :
    run 8 s = restored s := by
  have upper : Aligned (r (.GPR 31#5) s + 224#64) 4 := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr,
      Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  rw [restored]
  apply runs restoreOps s base code error
  change r .PC s = base + 1088#64 at pc
  simp (config := {decide := true}) [Follows, restoreOps, Op.row, Op.effect,
    restore, put, next, state_simp_rules, CheckSPAlignment, read_gpr,
    BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned upper ⊢
  exact ⟨aligned, upper⟩

/-- An internal observation obtained from the real saves and a body frame. -/
structure RestoreReady (entry current : ArmState) : Prop where
  stack : r (.GPR 31#5) current = bodySP entry
  saved : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 (bodySP entry + BitVec.ofNat 64 offset) current = r (.GPR reg) entry
  x18 : r (.GPR 18#5) current = r (.GPR 18#5) entry
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) entry).setWidth 64

theorem restored_returns (entry s : ArmState) (ready : RestoreReady entry s)
    (error : read_err s = .None) (program : s.program = entry.program) :
    SszArm.Emit.Returned entry (restored s) := by
  have h29 := ready.saved 29#5 128 (by decide)
  have h30 := ready.saved 30#5 136 (by decide)
  have h28 := ready.saved 28#5 144 (by decide)
  have h27 := ready.saved 27#5 152 (by decide)
  have h26 := ready.saved 26#5 160 (by decide)
  have h25 := ready.saved 25#5 168 (by decide)
  have h24 := ready.saved 24#5 176 (by decide)
  have h23 := ready.saved 23#5 184 (by decide)
  have h22 := ready.saved 22#5 192 (by decide)
  have h21 := ready.saved 21#5 200 (by decide)
  have h20 := ready.saved 20#5 208 (by decide)
  have h19 := ready.saved 19#5 216 (by decide)
  constructor
  · simp [restored, restoreOps, block, Op.effect, restore, put, next,
      state_simp_rules, BitVec.add_assoc, ready.stack, h30]
  · exact (restored_error s).trans error
  · exact (restored_program s).trans program
  · simp [restored, restoreOps, block, Op.effect, restore, put, next,
      state_simp_rules, ready.stack, bodySP, BitVec.sub_add_cancel]
  · intro reg low high
    have members : reg = 18#5 ∨ reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨ reg = 27#5 ∨
        reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by bv_omega
    rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [restored, restoreOps, block, Op.effect, restore, put, next,
        state_simp_rules, BitVec.add_assoc, ready.stack, h30, h29, h28, h27,
        h26, h25, h24, h23, h22, h21, h20, h19, ready.x18]
  · intro reg low high
    rw [restored_vector]
    exact ready.vectors reg low high

end SszArm.Codec.Emit.Parts
