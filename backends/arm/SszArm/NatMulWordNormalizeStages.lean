import SszArm.NatMulWordNormalizeFrame
import SszArm.WordNormalize

namespace SszArm.NatMulWord

open UintCodec

def normalizeGuard : List Op := [.p1468, .p1472]
def normalizeRoundOps : List Op := [.p1468, .p1472, .p1476, .p1480]

def normalizeRound (base : BitVec 64) (s : ArmState) : ArmState :=
  block base normalizeRoundOps s

private theorem count_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1468.effect base s) =
      if reg = 12#5 then r (.GPR 12#5) s - 1#64 else r (.GPR reg) s := by
  have different (flag : PFlag) : StateField.GPR reg ≠ .FLAG flag := by
    intro equal
    cases equal
  simp only [Op.effect, write_pstate, put, next,
    r_of_w_different (different .V), r_of_w_different (different .C),
    r_of_w_different (different .Z), r_of_w_different (different .N),
    NatCompare.r_gpr_of_w_gpr, NatCompare.r_gpr_of_w_pc] <;> arm_word_nf

private theorem count_zero (s : ArmState) (base : BitVec 64) :
    r (.FLAG .Z) (Op.p1468.effect base s) =
      (AddWithCarry (r (.GPR 12#5) s) (~~~1#64) 1#1).2.z := by
  simp only [Op.effect, write_pstate,
    r_of_w_different (show StateField.FLAG .Z ≠ .FLAG .V from by decide),
    r_of_w_different (show StateField.FLAG .Z ≠ .FLAG .C from by decide), r_of_w_same]

private theorem guard_branch_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1472.effect base s) = r (.GPR reg) s := by
  simp only [Op.effect, NatCompare.r_gpr_of_w_pc]

private theorem tail_branch_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1480.effect base s) = r (.GPR reg) s := by
  simp only [Op.effect, NatCompare.r_gpr_of_w_pc]

private theorem guard_branch_pc (s : ArmState) (base : BitVec 64) :
    read_pc (Op.p1472.effect base s) =
      if r (.FLAG .Z) s = 1#1 then base + 1544#64 else base + 1476#64 := by
  simp only [Op.effect, read_pc, r_of_w_same]

private theorem tail_branch_pc (s : ArmState) (base : BitVec 64) :
    read_pc (Op.p1480.effect base s) =
      if r (.GPR 9#5) s = 0#64 then base + 1468#64 else base + 1484#64 := by
  simp only [Op.effect, read_pc, r_of_w_same]

private theorem load_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1476.effect base s) =
      if reg = 8#5 then r (.GPR 8#5) s + (-8#64)
      else if reg = 9#5 then read_mem_bytes 8 (r (.GPR 8#5) s) s
      else r (.GPR reg) s := by
  simp only [Op.effect, put, next, NatCompare.r_gpr_of_w_gpr,
    NatCompare.r_gpr_of_w_pc] <;> arm_word_nf

theorem normalize_guard_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base normalizeGuard s) =
      if reg = 12#5 then r (.GPR 12#5) s - 1#64 else r (.GPR reg) s := by
  change r (.GPR reg) (Op.p1472.effect base (Op.p1468.effect base s)) = _
  rw [guard_branch_gpr, count_gpr]

theorem normalize_guard_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base normalizeGuard s) =
      if r (.GPR 12#5) s = 1#64 then base + 1544#64 else base + 1476#64 := by
  change read_pc (Op.p1472.effect base (Op.p1468.effect base s)) = _
  rw [guard_branch_pc, count_zero]
  simp only [Udivti3.cmp_zero]

private theorem guard_load (s : ArmState) (base address : BitVec 64) :
    read_mem_bytes 8 address (block base normalizeGuard s) = read_mem_bytes 8 address s := by
  have frame := normalize_read_frame base normalizeGuard s (by decide)
  apply BoolCodec.read_bytes_congr
  intro j hj
  exact congrFun frame.memory _

theorem normalize_round_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (normalizeRound base s) =
      if reg = 8#5 then r (.GPR 8#5) s + (-8#64)
      else if reg = 9#5 then read_mem_bytes 8 (r (.GPR 8#5) s) s
      else if reg = 12#5 then r (.GPR 12#5) s - 1#64
      else r (.GPR reg) s := by
  change r (.GPR reg)
    (Op.p1480.effect base (Op.p1476.effect base (block base normalizeGuard s))) = _
  rw [tail_branch_gpr, load_gpr]
  simp only [normalize_guard_gpr]
  arm_word_nf
  simp only [show (8#5 : BitVec 5) ≠ 12#5 by decide, ↓reduceIte, guard_load]

theorem normalize_round_pc (s : ArmState) (base : BitVec 64) :
    read_pc (normalizeRound base s) =
      if read_mem_bytes 8 (r (.GPR 8#5) s) s = 0#64 then base + 1468#64 else base + 1484#64 := by
  change read_pc
    (Op.p1480.effect base (Op.p1476.effect base (block base normalizeGuard s))) = _
  rw [tail_branch_pc, load_gpr]
  simp only [normalize_guard_gpr]
  arm_word_nf
  simp only [show (9#5 : BitVec 5) ≠ 8#5 by decide,
    show (8#5 : BitVec 5) ≠ 12#5 by decide, ↓reduceIte, guard_load]

theorem normalize_guard_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 1468#64) : Follows base normalizeGuard s := by
  have hpc : r .PC s = base + 1468#64 := hp
  simp [normalizeGuard, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem normalize_round_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 1468#64) (nonzero : r (.GPR 12#5) s ≠ 1#64) :
    Follows base normalizeRoundOps s := by
  have hpc : r .PC s = base + 1468#64 := hp
  simp [normalizeRoundOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, nonzero, BitVec.add_assoc]

end SszArm.NatMulWord
