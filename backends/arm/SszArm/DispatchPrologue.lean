import SszArm.DispatchBlocks
import SszArm.BoolActivation
import SszArm.UintResultMemory

namespace SszArm.Dispatch

open Block

def bodySP (s : ArmState) : BitVec 64 := r (.GPR 31#5) s - 368#64

def prologueOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p20, .p24]

def prologue (s : ArmState) : ArmState := Block.effect prologueOps s

/-- The only bytes written before tag dispatch: the six original register pairs. -/
def savedMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 352#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
  (write_mem_bytes 16 (bodySP s + 336#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
  (write_mem_bytes 16 (bodySP s + 320#64) (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
  (write_mem_bytes 16 (bodySP s + 304#64) (r (.GPR 25#5) s ++ r (.GPR 26#5) s)
  (write_mem_bytes 16 (bodySP s + 288#64) (r (.GPR 27#5) s ++ r (.GPR 28#5) s)
  (write_mem_bytes 16 (bodySP s + 272#64) (r (.GPR 30#5) s ++ r (.GPR 29#5) s) s)))))

@[simp] theorem prologue_sp (s : ArmState) : r (.GPR 31#5) (prologue s) = bodySP s := by
  simp [prologue, prologueOps, Block.effect, Op.effect, put, next, save, bodySP, state_simp_rules]

@[simp] theorem prologue_reg (s : ArmState) (reg : BitVec 5) (different : reg ≠ 31#5) :
    r (.GPR reg) (prologue s) = r (.GPR reg) s := by
  simp [prologue, prologueOps, Block.effect, Op.effect, put, next, save, different, state_simp_rules]

@[simp] theorem prologue_pc (s : ArmState) : read_pc (prologue s) = read_pc s + 28#64 := by
  simp [prologue, prologueOps, Block.effect, Op.effect, put, next, save,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (s : ArmState) : (prologue s).program = s.program := by
  simp [prologue, prologueOps, Block.effect]

@[simp] theorem prologue_error (s : ArmState) : read_err (prologue s) = read_err s := by
  simp [prologue, prologueOps, Block.effect]

@[simp] theorem prologue_memory (s : ArmState) : (prologue s).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, Block.effect, Op.effect, put, next, save,
    savedMemory, bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem prologue_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (prologue s) = r (.SFP reg) s := by
  simp [prologue, prologueOps, Block.effect, Op.effect, put, next, save, state_simp_rules]

theorem bodySP_aligned (s : ArmState) (aligned : CheckSPAlignment s) : Aligned (bodySP s) 4 := by
  simp (config := {decide := true}) [CheckSPAlignment, read_gpr, bodySP,
    Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
  bv_omega

theorem prologue_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (prologue s) :=
  CheckSPAlignment_of_r_sp_aligned (prologue_sp s) (bodySP_aligned s aligned)

/-- Seven actual instructions allocate and initialize the saved activation. -/
theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 7 s = prologue s := by
  have afterSP := bodySP_aligned s aligned
  have follows : Follows base prologueOps s := by
    change r .PC s = base at pc
    simp (config := {decide := true}) [Follows, prologueOps, Op.row, Op.effect,
      put, next, save, state_simp_rules, CheckSPAlignment, read_gpr,
      BitVec.setWidth_eq, bodySP, pc, BitVec.add_assoc] at aligned afterSP ⊢
    exact ⟨aligned, afterSP⟩
  exact Block.runs prologueOps s base code error follows

/-- The original entry has a mapped stack interval; prologue writes cannot wrap. -/
theorem prologue_frame (s : ArmState) (low : 368 ≤ (r (.GPR 31#5) s).toNat)
    (a : BitVec 64)
    (outside : a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (prologue s).mem a = s.mem a := by
  rw [prologue_memory]
  simp only [savedMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ a (by simp only [bodySP]; bv_omega)
    (by simp only [bodySP]; bv_omega)]

/-- Every common RET load now refers to the corresponding original register. -/
theorem prologue_saved (s : ArmState) (low : 368 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ BoolCodec.savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (prologue s) = r (.GPR reg) s := by
  have memory : ∀ n address, read_mem_bytes n address (prologue s) =
      read_mem_bytes n address (savedMemory s) := by
    intro n address
    apply BoolCodec.read_bytes_congr
    intro i hi
    exact congrFun (prologue_memory s) _
  rw [memory]
  simp only [BoolCodec.savedRegisters, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at member
  rcases member with member | member | member | member | member | member |
    member | member | member | member | member | member
  all_goals
    rcases member with ⟨rfl, rfl⟩
    simp only [savedMemory]
    simp (disch := (simp only [bodySP]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

end SszArm.Dispatch
