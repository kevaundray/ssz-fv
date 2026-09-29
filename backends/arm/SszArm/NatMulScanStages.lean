import SszArm.NatMulScanLoad
import SszArm.WordNormalize

namespace SszArm.NatMul

/-- Keep the pure scan control stages opaque to the unbounded induction. -/
theorem left_head_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 40#64) : Follows base [.p40, .p44] s := by
  have hpc : r .PC s = base + 40#64 := hp
  arm_word_nf at hpc
  simp only [Follows, Op.row, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

theorem left_head_values (s : ArmState) (base : BitVec 64) :
    let t := block base [.p40, .p44] s
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 9#5) t = r (.GPR 10#5) s ∧
    read_pc t = base + (if r (.GPR 10#5) s = 0#64 then 124#64 else 48#64) := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [apply_ite]

theorem left_tail_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 80#64) : Follows base [.p80, .p84] s := by
  have hpc : r .PC s = base + 80#64 := hp
  arm_word_nf at hpc
  simp only [Follows, Op.row, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

theorem left_tail_values (s : ArmState) (base : BitVec 64) :
    let t := block base [.p80, .p84] s
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 9#5) t = r (.GPR 9#5) s ∧
    r (.GPR 10#5) t = r (.GPR 9#5) s - 1#64 ∧
    read_pc t = base + (if r (.GPR 11#5) s = 0#64 then 40#64 else 88#64) := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [apply_ite]

theorem scan_left_load_values (s : ArmState) (base word : BitVec 64) :
    let t := scanLoadResult s base .left word
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 9#5) t = r (.GPR 9#5) s ∧
    r (.GPR 11#5) t = word ∧ read_pc t = base + 80#64 := by
  simp only [scanLoadResult, ScanLoad.start, ScanLoad.size, ScanLoad.dst,
    NatCompare.saved, read_pc]
  arm_state_nf
  all_goals simp

def leftScanRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p80, .p84]
    (scanLoadResult (block base [.p40, .p44] s) base .left word)

theorem left_round_values (s : ArmState) (base word : BitVec 64) :
    let t := leftScanRound s base word
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 9#5) t = r (.GPR 10#5) s ∧
    r (.GPR 10#5) t = r (.GPR 10#5) s - 1#64 ∧
    read_pc t = base + (if word = 0#64 then 40#64 else 88#64) := by
  obtain ⟨head8, head9, headPC⟩ := left_head_values s base
  obtain ⟨load8, load9, load11, loadPC⟩ :=
    scan_left_load_values (block base [.p40, .p44] s) base word
  obtain ⟨tail8, tail9, tail10, tailPC⟩ :=
    left_tail_values (scanLoadResult (block base [.p40, .p44] s) base .left word) base
  exact ⟨tail8.trans (load8.trans head8), tail9.trans (load9.trans head9),
    tail10.trans (congrArg (fun n => n - 1#64) (load9.trans head9)),
    tailPC.trans (congrArg (fun value : BitVec 64 =>
      base + (if value = 0#64 then 40#64 else 88#64)) load11)⟩

theorem left_entry_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 28#64) (nonzero : r (.GPR 1#5) s ≠ 0#64) :
    Follows base [.p28, .p32, .p36] s := by
  have hpc : r .PC s = base + 28#64 := hp
  arm_word_nf at hpc nonzero
  simp only [Follows, Op.row, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [hpc, nonzero, BitVec.add_assoc]

theorem left_entry_values (s : ArmState) (base : BitVec 64)
    (nonzero : r (.GPR 1#5) s ≠ 0#64) :
    let t := block base [.p28, .p32, .p36] s
    read_pc t = base + 40#64 ∧
    r (.GPR 8#5) t = r (.GPR 1#5) s - 8#64 ∧
    r (.GPR 10#5) t = r (.GPR 2#5) s := by
  arm_word_nf at nonzero
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [nonzero, BitVec.add_assoc]

end SszArm.NatMul
