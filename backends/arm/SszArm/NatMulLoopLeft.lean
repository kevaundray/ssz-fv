import SszArm.NatMulLoopControl

namespace SszArm.NatMul

open Delimited (MemoryFrame)

private theorem left_indexed_run (s : ArmState) (base value : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 612#64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (observed : read_mem_bytes 8 (r (.GPR 9#5) s + (r (.GPR 12#5) s <<< 3))
      (NatCompare.saved s 10#5) = value) :
    run 8 s = w .PC (base + 644#64) (w (.GPR 14#5) value (NatCompare.saved s 10#5)) := by
  have hpc : r .PC s = base + 612#64 := pc
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 10#5) = r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have follows : Follows base [.p612, .p616, .p620, .p624, .p628, .p632, .p636, .p640] s := by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = ([Op.p612, .p616, .p620, .p624, .p628, .p632, .p636, .p640]).length from rfl,
    block_run base _ s code error aligned follows]
  have effect := NatAdd.indexedReadSequence_eq s 9#5 12#5 10#5 14#5 value
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    observed restored
  change NatAdd.indexedReadSequence s 9#5 12#5 10#5 14#5 = _
  simpa only [pc, BitVec.add_assoc, show (612#64 + 32#64) = 644#64 by decide] using effect

private theorem left_block_vectors (base : BitVec 64) (ops : List Op)
    (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block base ops s) = r (.SFP reg) s := by
  exact NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (r (.SFP reg)) ops s (fun op _ t => op.sfp base t reg)

private theorem left_small_stable (s : ArmState) (base : BitVec 64) :
    LoopStable [14#5] s (block base [.p600, .p648, .p652, .p656] s) := by
  constructor
  · simp
  · simp
  · simp only [block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg different
    have different' : reg ≠ 14#5 := by simpa using different
    simp only [block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, different']
  · intro reg
    exact left_block_vectors base _ s reg

private theorem left_small_observations (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p600, .p648, .p652, .p656] s) = base + 664#64 ∧
    r (.GPR 14#5) (block base [.p600, .p648, .p652, .p656] s) =
      (if r (.GPR 12#5) s = 0#64 then r (.GPR 10#5) s else 0#64) ∧
    (block base [.p600, .p648, .p652, .p656] s).mem = s.mem := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, Udivti3.cmp_zero]

private theorem left_checked_stable (s : ArmState) (base : BitVec 64) :
    LoopStable [] s (block base [.p600, .p604, .p608] s) := by
  constructor
  · simp
  · simp
  · simp only [block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg different
    simp only [block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg
    exact left_block_vectors base _ s reg

private theorem left_checked_memory (s : ArmState) (base : BitVec 64) :
    (block base [.p600, .p604, .p608] s).mem = s.mem := by
  simp only [block, List.foldl_cons, List.foldl_nil]
  simp [Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]

/-- Original +600..+660 Nat::word choice, including small and out-of-range
representations. The source list is the full raw allocation, not its trim. -/
theorem loop_left_run (s : ArmState) (base : BitVec 64) (words : List (BitVec 64))
    (index : Nat) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 600#64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (indexBound : index < 2^64)
    (row : r (.GPR 12#5) s = BitVec.ofNat 64 index)
    (operand : NatCompare.Operand s (r (.GPR 9#5) s) (r (.GPR 10#5) s) words) :
    ∃ fuel t, run fuel s = t ∧ LoopStable [14#5] s t ∧
      MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s t ∧
      read_pc t = base + 664#64 ∧ r (.GPR 14#5) t = words[index]?.getD 0#64 := by
  have hpc : r .PC s = base + 600#64 := pc
  by_cases small : r (.GPR 9#5) s = 0#64
  · have raw := operand.small small
    let ops : List Op := [.p600, .p648, .p652, .p656]
    have executes : run 4 s = block base ops s := by
      apply block_run base ops s code error aligned
      simp [ops, Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, hpc, small, BitVec.add_assoc]
    have observations := left_small_observations s base
    refine ⟨4, block base ops s, executes, left_small_stable s base, ?_,
      observations.1, ?_⟩
    · intro address outside
      exact congrFun observations.2.2 address
    · rw [observations.2.1, row, raw]
      have zero : BitVec.ofNat 64 index = 0#64 ↔ index = 0 := by bv_omega
      cases index with
      | zero => simp
      | succ index => simp [zero]
  · obtain ⟨length, source, memory⟩ := operand.large small
    let u := block base [.p600, .p604, .p608] s
    have runU : run 3 s = u := by
      apply block_run base [.p600, .p604, .p608] s code error aligned
      simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, hpc, small, BitVec.add_assoc]
    have uf : LoopStable [] s u := left_checked_stable s base
    have um : u.mem = s.mem := left_checked_memory s base
    have branch : (AddWithCarry (r (.GPR 12#5) s) (~~~r (.GPR 10#5) s) 1#1).2.c = 1#1 ↔
        words.length ≤ index := by
      rw [Udivti3.cmp_carry, row, length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
    by_cases beyond : words.length ≤ index
    · have up : read_pc u = base + 660#64 := by
        simp only [u, block, List.foldl_cons, List.foldl_nil]
        simp [Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules, branch, beyond]
      let t := Op.p660.effect base u
      have runT : run 1 u = t := by
        change stepi u = t
        exact step u base .p660 (uf.code code) up (uf.error.trans error) (uf.aligned aligned)
      refine ⟨3 + 1, t, by rw [run_plus, runU, runT], ?_, ?_, ?_, ?_⟩
      · constructor
        · simp [t, uf.program]
        · simp [t, uf.error]
        · simpa [t, Op.effect, put, next, state_simp_rules] using uf.sp
        · intro reg different
          have different' : reg ≠ 14#5 := by simpa using different
          calc
            r (.GPR reg) t = r (.GPR reg) u := by
              simp [t, Op.effect, put, next, state_simp_rules, different']
            _ = r (.GPR reg) s := uf.registers reg (by simp)
        · intro reg
          simp [t, uf.vectors]
      · intro address outside
        simpa [t, Op.effect, put, next, state_simp_rules] using congrFun um address
      · have upc : r .PC u = base + 660#64 := up
        simp [t, Op.effect, put, next, state_simp_rules, upc, BitVec.add_assoc]
      · simp [t, Op.effect, put, next, state_simp_rules, List.getElem?_eq_none beyond]
    · have inside : index < words.length := by omega
      have up : read_pc u = base + 612#64 := by
        simp only [u, block, List.foldl_cons, List.foldl_nil]
        simp [Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules, branch, beyond]
      have us : NatCompare.Source u (r (.GPR 9#5) u) words := by
        have sameStack : r (.GPR 31) u = r (.GPR 31) s := uf.sp
        simpa only [NatCompare.Source, ByteView.Source, sameStack,
          uf.registers 9#5 (by simp)] using source
      have uw : NatCompare.Words u (r (.GPR 9#5) u) words := by
        intro i
        rw [uf.registers 9#5 (by simp), Memory.mem_eq_iff_read_mem_bytes_eq.mp um]
        exact memory i
      have observed : read_mem_bytes 8 (r (.GPR 9#5) u + (r (.GPR 12#5) u <<< 3))
          (NatCompare.saved u 10#5) = words[index]?.getD 0#64 := by
        rw [uf.registers 12#5 (by simp), row]
        exact NatCompare.limb_load u (r (.GPR 9#5) u) words index 10#5 inside us uw
      let v := w .PC (base + 644#64)
        (w (.GPR 14#5) (words[index]?.getD 0#64) (NatCompare.saved u 10#5))
      have runV : run 8 u = v := left_indexed_run u base _ (uf.code code)
        (uf.error.trans error) (uf.aligned aligned) up us.1 observed
      have vf : LoopStable [14#5] u v := by
        constructor
        · simp [v, NatCompare.saved, state_simp_rules]
        · simp [v, NatCompare.saved, state_simp_rules]
        · simp [v, NatCompare.saved, state_simp_rules]
        · intro reg different
          have different' : reg ≠ 14#5 := by simpa using different
          simp [v, NatCompare.saved, state_simp_rules, different']
        · intro reg
          simp [v, NatCompare.saved, state_simp_rules]
      let t := w .PC (base + 664#64) v
      have runT : run 1 v = t := by
        change stepi v = t
        exact step v base .p644 (vf.code (uf.code code))
          (by simp [v, Op.row, state_simp_rules]) (vf.error.trans (uf.error.trans error))
          (vf.aligned (uf.aligned aligned))
      refine ⟨3 + 8 + 1, t, by rw [run_plus, run_plus, runU, runV, runT], ?_, ?_, ?_, ?_⟩
      · have tf : LoopStable [14#5] v t := by
          constructor <;> simp [t, state_simp_rules]
        exact (uf.weaken (by simp)).trans (vf.trans tf)
      · intro address outside
        have separate := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
        simp only [t, v, ArmState.mem_w_eq_mem, NatCompare.saved]
        exact (BoolCodec.write_mem_bytes_frame u _ 8 _ address (by rw [uf.sp]; bv_omega)
          (by rw [uf.sp]; bv_omega)).trans (congrFun um address)
      · simp [t, state_simp_rules]
      · simp [t, v, state_simp_rules]

end SszArm.NatMul
