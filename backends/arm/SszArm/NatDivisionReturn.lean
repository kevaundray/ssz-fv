import SszArm.NatDivisionActivation

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame Returned)
open BoolCodec
open UintCodec.Tail

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The common suffix writes the selected final word and status, restores the
six saved nonvolatile registers and original LR, and executes RET. -/
def returnOps : List Op :=
  [.p976, .p980, .p984, .p988, .p992, .p996, .p1000, .p1004,
   .p1008, .p1012, .p1016, .p1020, .p1024]

structure ReturnSpace (s : ArmState) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 64 ≤ 2^64
  outputHigh : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64
  separate : (r (.GPR 19#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat + 64 ≤ (r (.GPR 19#5) s).toNat

macro "division_return_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [block, returnOps, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem return_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 976#64) :
    run 13 s = block base returnOps s := by
  apply block_run base returnOps s hc he ha
  have hpc : r .PC s = base + 976#64 := hp
  simp (config := {decide := true, instances := true})
    [returnOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def returnWrites (s : ArmState) : List Span :=
  [((r (.GPR 19#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 16, 16)]

theorem return_frame (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64) :
    MemoryFrame (returnWrites s) s (block base returnOps s) := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  intro a ha
  have outsideOutput := ha ((r (.GPR 19#5) s).toNat, 68) (by simp [returnWrites])
  have outsideStack := ha ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [returnWrites])
  simp only [Prod.fst, Prod.snd] at outsideOutput outsideStack
  rcases index with index | index
  all_goals
    division_return_expand
    rw [index]
    simp (disch := tail_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

/-- Both branch-selected output words are retained, even on the failure path
where the selected word is the error text length rather than a remainder. -/
theorem return_word (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64) :
    read_mem_bytes 8 (r (.GPR 19#5) s + r (.GPR 9#5) s)
      (block base returnOps s) = r (.GPR 1#5) s := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  rcases index with index | index
  all_goals
    division_return_expand
    rw [index]
    tail_reads

theorem return_status (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64) :
    read_mem_bytes 4 (r (.GPR 19#5) s + 64#64)
      (block base returnOps s) = (r (.GPR 8#5) s).setWidth 32 := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  rcases index with index | index
  all_goals
    division_return_expand
    rw [index]
    tail_reads

/-- The final RET targets the original LR despite every intervening BL. -/
theorem return_restores (original s : ArmState) (base : BitVec 64)
    (saved : Saved original s) (space : ReturnSpace s)
    (index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64)
    (error : read_err s = .None) :
    Delimited.Returned original (block base returnOps s) := by
  have h30 := saved.words 30#5 0 (by decide)
  have h24 := saved.words 24#5 16 (by decide)
  have h23 := saved.words 23#5 24 (by decide)
  have h22 := saved.words 22#5 32 (by decide)
  have h21 := saved.words 21#5 40 (by decide)
  have h20 := saved.words 20#5 48 (by decide)
  have h19 := saved.words 19#5 56 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h30 h24 h23 h22 h21 h20 h19
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  constructor
  · rcases index with index | index
    all_goals
      division_return_expand
      rw [index]
      tail_reads
      exact h30
  · exact (block_error _ _ _).trans error
  · division_return_expand
    rw [saved.sp]
    bv_omega
  · intro reg low high
    have members : reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨
        reg = 27#5 ∨ reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by bv_omega
    rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rcases index with index | index
      all_goals
        division_return_expand
        try rw [index]
        try tail_reads
        try simp only [h19, h20, h21, h22, h23, h24, h30]
    all_goals exact saved.high _ (by decide) (by decide)
  · intro reg low high
    simpa [block, returnOps, Op.effect, put, next, state_simp_rules] using
      saved.vectors reg low high

end SszArm.NatDivision
