import SszArm.DelimitedBlocks
import SszArm.DelimitedZeroMemory

namespace SszArm.Delimited

open BoolCodec
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

structure EmptyOwned (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 0#5) s).toNat + 76 ≤ 2^64
  disjoint : (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat

macro "empty_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [block, emptyOps, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel,
     BitVec.reduceAppend, write_pair_ones, write_zero32, write_zero16])

macro "empty_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := delimited_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

theorem empty_body_result (s : ArmState) (base : BitVec 64) (owned : EmptyOwned s) :
    SszNative.BitView.ResultAt (widthLoad (block base emptyOps s))
      (r (.GPR 0#5) s).toNat (.error .emptyEncoding) := by
  rcases owned with ⟨stack, output, disjoint⟩
  change SszNative.UintCodec.errorAt _ _ 16 0 0
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    empty_expand
    empty_reads

theorem empty_body_returned (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) : Returned s (block base emptyOps s) := by
  constructor
  · simp [block, emptyOps, Op.effect, put, next, state_simp_rules]
  · exact (block_error _ _ _).trans he
  · simp [block, emptyOps, Op.effect, put, next, state_simp_rules, BitVec.sub_add_cancel]
  · intro reg low high
    have ne8 : reg ≠ 8#5 := by bv_omega
    have ne9 : reg ≠ 9#5 := by bv_omega
    have ne10 : reg ≠ 10#5 := by bv_omega
    have ne31 : reg ≠ 31#5 := by bv_omega
    simp [block, emptyOps, Op.effect, put, next, state_simp_rules, ne8, ne9, ne10, ne31]
  · intro reg low high
    have ne : reg ≠ 0#5 := by bv_omega
    simp [block, emptyOps, Op.effect, put, next, state_simp_rules, ne]

theorem empty_body_frame (s : ArmState) (base : BitVec 64)
    (owned : EmptyOwned s) (empty : r (.GPR 3#5) s = 0#64) :
    MemoryFrame (localWrites s) s (block base emptyOps s) := by
  rcases owned with ⟨stack, output, disjoint⟩
  intro a ha
  have out := ha ((r (.GPR 0#5) s).toNat, 76) (by simp [localWrites])
  have work := ha (activationSpan s) (by simp [localWrites])
  simp only [Prod.fst, Prod.snd, activationSpan, empty, ↓reduceIte] at out work
  empty_expand
  simp (disch := delimited_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

/-- Full real entry-to-RET proof for the empty encoding. The error path performs
its SIMD zero stores and sixteen-byte lowering save, but never reads the option,
input pointer, or arena and never advances the caller's scratch cursor. -/
theorem empty_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry)
    (empty : r (.GPR 3#5) s = 0#64) (owned : EmptyOwned s) :
    ∃ t, run 19 s = t ∧ Returned s t ∧ MemoryFrame (localWrites s) s t ∧
      SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (.error .emptyEncoding) := by
  let u := Op.p0.effect base s
  have first : stepi s = u := step s base .p0 hc (by simpa [entry, Op.row] using hp) he ha
  have pc : read_pc u = base + 196#64 := by simp [u, Op.effect, empty, state_simp_rules]
  have code : CodeAt u base := by simpa only [u, CodeAt, Op.program] using hc
  have err : read_err u = .None := by simpa only [u, Op.error] using he
  have align : CheckSPAlignment u := Op.aligned .p0 base s ha
  have ownership : EmptyOwned u := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [u, Op.effect, state_simp_rules] using owned.stack
    · simpa [u, Op.effect, state_simp_rules] using owned.output
    · simpa [u, Op.effect, state_simp_rules] using owned.disjoint
  have isempty : r (.GPR 3#5) u = 0#64 := by simpa [u, Op.effect, state_simp_rules] using empty
  let t := block base emptyOps u
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · rw [show 19 = 18 + 1 by decide, run, first]
    exact empty_run u base code err align pc
  · have returned := empty_body_returned u base err
    refine ⟨?_, returned.error, ?_, ?_, ?_⟩
    · simpa [t, u, Op.effect, state_simp_rules] using returned.pc
    · simpa [t, u, Op.effect, state_simp_rules] using returned.sp
    · intro reg low high
      simpa [t, u, Op.effect, state_simp_rules] using returned.registers reg low high
    · intro reg low high
      simpa [t, u, Op.effect, state_simp_rules] using returned.vectors reg low high
  · have frame := empty_body_frame u base ownership isempty
    simpa [MemoryFrame, localWrites, activationSpan, t, u, Op.effect, state_simp_rules] using frame
  · have result := empty_body_result u base ownership
    simpa [t, u, Op.effect, state_simp_rules] using result

end SszArm.Delimited
