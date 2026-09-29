import SszArm.NatMulScanLeft

namespace SszArm.NatMul

/-- Right-scan observations are proved at bounded instruction cuts. -/
theorem right_head_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 164#64) (nonzero : r (.GPR 9#5) s ≠ 0#64) :
    Follows base [.p164, .p168, .p172] s := by
  have hpc : r .PC s = base + 164#64 := hp
  arm_word_nf at hpc nonzero
  simp only [Follows, Op.row, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [hpc, nonzero, BitVec.add_assoc]

theorem right_head_values (s : ArmState) (base : BitVec 64)
    (nonzero : r (.GPR 9#5) s ≠ 0#64) :
    let t := block base [.p164, .p168, .p172] s
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 21#5) t = r (.GPR 21#5) s ∧
    r (.GPR 9#5) t = r (.GPR 3#5) s + (r (.GPR 9#5) s <<< 3) ∧
    r (.GPR 22#5) t = r (.GPR 9#5) s ∧ read_pc t = base + 176#64 := by
  arm_word_nf at nonzero
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [nonzero, BitVec.add_assoc]

theorem right_tail_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 204#64) : Follows base [.p204, .p208] s := by
  have hpc : r .PC s = base + 204#64 := hp
  arm_word_nf at hpc
  simp only [Follows, Op.row, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

theorem right_tail_values (s : ArmState) (base : BitVec 64) :
    let t := block base [.p204, .p208] s
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 21#5) t = r (.GPR 21#5) s ∧
    r (.GPR 9#5) t = r (.GPR 22#5) s - 1#64 ∧
    r (.GPR 22#5) t = r (.GPR 22#5) s ∧
    read_pc t = base + (if r (.GPR 10#5) s = 0#64 then 164#64 else 212#64) := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [apply_ite]

theorem scan_right_load_values (s : ArmState) (base word : BitVec 64) :
    let t := scanLoadResult s base .right word
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 21#5) t = r (.GPR 21#5) s ∧
    r (.GPR 22#5) t = r (.GPR 22#5) s ∧
    r (.GPR 10#5) t = word ∧ read_pc t = base + 204#64 := by
  simp only [scanLoadResult, ScanLoad.start, ScanLoad.size, ScanLoad.dst,
    NatCompare.saved, read_pc]
  arm_state_nf
  all_goals simp

def rightScanRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p204, .p208]
    (scanLoadResult (block base [.p164, .p168, .p172] s) base .right word)

theorem right_round_values (s : ArmState) (base word : BitVec 64)
    (nonzero : r (.GPR 9#5) s ≠ 0#64) :
    let t := rightScanRound s base word
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 21#5) t = r (.GPR 21#5) s ∧
    r (.GPR 9#5) t = r (.GPR 9#5) s - 1#64 ∧
    r (.GPR 22#5) t = r (.GPR 9#5) s ∧
    read_pc t = base + (if word = 0#64 then 164#64 else 212#64) := by
  obtain ⟨head8, head21, head9, head22, headPC⟩ := right_head_values s base nonzero
  obtain ⟨load8, load21, load22, load10, loadPC⟩ :=
    scan_right_load_values (block base [.p164, .p168, .p172] s) base word
  obtain ⟨tail8, tail21, tail9, tail22, tailPC⟩ :=
    right_tail_values (scanLoadResult (block base [.p164, .p168, .p172] s) base .right word) base
  exact ⟨tail8.trans (load8.trans head8), tail21.trans (load21.trans head21),
    tail9.trans (congrArg (fun n => n - 1#64) (load22.trans head22)),
    tail22.trans (load22.trans head22),
    tailPC.trans (congrArg (fun value : BitVec 64 =>
      base + (if value = 0#64 then 164#64 else 212#64)) load10)⟩

theorem right_zero_values (s : ArmState) (base : BitVec 64)
    (zero : r (.GPR 9#5) s = 0#64) :
    let t := block base [.p164] s
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 21#5) t = r (.GPR 21#5) s ∧ read_pc t = base + 264#64 := by
  arm_word_nf at zero
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, read_pc]
  arm_state_nf
  all_goals simp [zero]

theorem right_entry_values (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 160#64) :
    let t := block base [.p160] s
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 21#5) t = r (.GPR 21#5) s ∧
    r (.GPR 9#5) t = r (.GPR 4#5) s ∧ read_pc t = base + 164#64 := by
  have hpc : r .PC s = base + 160#64 := hp
  arm_word_nf at hpc
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

end SszArm.NatMul
