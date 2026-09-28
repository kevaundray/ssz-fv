import SszX86.BitVectorErrorsWorld
import SszX86.BitVectorDivisionStage

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- These are the four real loads used by the native division-result staging block. -/
theorem division_error_loads (m : DataMem) (sp : UInt64) (reason : NatArithmetic.Failure)
    (observed : NatArithmetic.errorAt (widthLoad m) (sp.toNat + 16) reason) :
    Mem.loadInt m (sp.toBitVec + 80#64) 4 =
      some ((arithmeticErrorImage reason 0).reason.toNat : Int) ∧
    Mem.loadInt m (sp.toBitVec + 16#64) 8 = some ((1#64).toNat : Int) ∧
    Mem.loadInt m (sp.toBitVec + 24#64) 8 = some ((0#64).toNat : Int) ∧
    Mem.loadInt m (sp.toBitVec + 32#64) 8 = some ((0#64).toNat : Int) := by
  rcases observed with ⟨h0, h1, h2, _, _, _, _, _, statusAt⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply errors_raw_read _ _ 80 4
    cases reason <;>
      simpa only [Nat.add_assoc, Nat.reduceAdd, arithmeticErrorImage,
        show (32768#32).toNat = 32768 by decide,
        show (32770#32).toNat = 32770 by decide] using statusAt
  · apply errors_raw_read _ _ 16 8
    simpa only [show (1#64).toNat = 1 by decide] using h0
  · apply errors_raw_read _ _ 24 8
    simpa only [Nat.add_assoc, Nat.reduceAdd, show (0#64).toNat = 0 by decide] using h1
  · apply errors_raw_read _ _ 32 8
    simpa only [Nat.add_assoc, Nat.reduceAdd, show (0#64).toNat = 0 by decide] using h2

/-- The native SP120/SP128 staging leaves the complete private error intact. -/
theorem division_error_private (s u : MachineData) (length : NatOperand)
    (anchors : Anchors s u length) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (reason : NatArithmetic.Failure) (flags : StatusFlags)
    (observed : NatArithmetic.errorAt (widthLoad u.dmem) (s.regs.rsp.toNat + 16) reason) :
    NatArithmetic.errorAt
      (widthLoad (divisionResultState u 1#64 0#64 0#64
        (arithmeticErrorImage reason 0).reason flags).dmem)
      (s.regs.rsp.toNat + 16) reason := by
  simpa (disch := decide) only [NatArithmetic.errorAt, Nat.add_assoc, Nat.reduceAdd,
    division_stage_private anchors high 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason flags]
    using observed

/-- No padding value or post-staging cache is assumed: the actual stage stores
and unchanged private loads establish the inputs of the raw error-copy suffix. -/
theorem division_error_staged_reads
    (s u : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (beforeAnchors : Anchors s u length) (reason : NatArithmetic.Failure) (flags : StatusFlags)
    (world : World s saved length data address capacity initialUsed currentUsed writes
      (divisionResultState u 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason flags).dmem)
    (anchors : Anchors s
      (divisionResultState u 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason flags) length)
    (observed : NatArithmetic.errorAt (widthLoad u.dmem) (s.regs.rsp.toNat + 16) reason) :
    ∃ padding : BitVec 32, DivisionErrorReads
      (divisionResultState u 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason flags) reason padding := by
  let v := divisionResultState u 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason flags
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at high
    omega
  have beforeLoads := division_error_loads u.dmem s.regs.rsp reason observed
  have keep (off count : Nat) (inside : off + count ≤ 120) :
      Mem.loadInt v.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count =
        Mem.loadInt u.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
    simpa only [v, divisionResultState, divisionResultMem, stackPairMem, beforeAnchors.stack] using
      stack_pair_read u.dmem s.regs.rsp.toBitVec 120 off count 1#64 0#64 highBV
        (by decide) (by omega) (Or.inl inside)
  have caches :
      Mem.loadInt v.dmem (s.regs.rsp.toBitVec + 120#64) 8 = some ((1#64).toNat : Int) ∧
      Mem.loadInt v.dmem (s.regs.rsp.toBitVec + 128#64) 8 = some ((0#64).toNat : Int) := by
    simpa only [v, divisionResultState, divisionResultMem, stackPairMem, beforeAnchors.stack] using
      stack_pair_reads u.dmem s.regs.rsp.toBitVec 120 1#64 0#64 highBV (by decide)
  have observedAfter := division_error_private s u length beforeAnchors high reason flags observed
  have statusRegister : v.regs.rax.toBitVec.setWidth 32 = (arithmeticErrorImage reason 0).reason := by
    change (((arithmeticErrorImage reason 0).reason).setWidth 64).setWidth 32 = _
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have stack : v.regs.rsp = s.regs.rsp := anchors.stack
  apply division_reads_of_private v reason
  · simpa only [NatArithmetic.DivisionResultAt, v, divisionResultState, beforeAnchors.stack]
      using observedAfter
  · have part := mapped_subrange v.dmem s.regs.rsp.toBitVec 224 16 72
      world.physical.body_mapped (by decide)
    simpa only [stack] using part
  · simpa only [statusRegister, stack] using (keep 80 4 (by decide)).trans beforeLoads.1
  · simpa only [stack] using
      caches.1.trans ((keep 16 8 (by decide)).trans beforeLoads.2.1).symm
  · simpa only [stack] using
      caches.2.trans ((keep 24 8 (by decide)).trans beforeLoads.2.2.1).symm
  · simpa only [v, divisionResultState, UInt64.toBitVec_ofBitVec, beforeAnchors.stack] using
      (keep 32 8 (by decide)).trans beforeLoads.2.2.2

end SszX86.BitVector
