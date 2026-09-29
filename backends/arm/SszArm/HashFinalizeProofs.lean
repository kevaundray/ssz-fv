import SszArm.HashFinalizePrefix
import SszArm.HashFinalizeOverflow
import SszArm.HashFinalizeReturn

namespace SszArm.Hash

open Finalize
open SszNative.HashStream (delimiterBuffer overflowBuffer finishBuffer compressBuffer finalizeRun)

/-- Actual entry-to-last-compression execution, including both zero-length memset boundaries. -/
theorem finalize_padding (s : ArmState) (base : BitVec 64) (value : StreamState)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + finalizeOffset) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : FinalizeOwned s base value) :
    ∃ fuel t, run fuel s = t ∧ Live s t ∧
      ChainingAt t (statePtr s + 64#64) (finalizeRun value).chaining ∧
      read_pc t = base + finalizeOffset + 216#64 := by
  obtain ⟨t, execution, live, stored, count, oldCount, next⟩ :=
    prefix s base value code error aligned owned pc
  by_cases one : value.buffered.val + 1 ≤ 56
  · have nextOne : read_pc t = base + finalizeOffset + 168#64 := by
      simpa only [one, if_pos] using next
    obtain ⟨fuel, u, executionU, liveU, storedU, pcU⟩ :=
      last_block s t base value (delimiterBuffer value) value.chaining value.byteLen
        (value.buffered.val + 1) one code data owned compression aligned live stored nextOne count
    refine ⟨21 + fuel, u, ?_, liveU, ?_, pcU⟩
    · rw [run_plus, execution, executionU]
    · have noSpill : ¬ 56 < value.buffered.val + 1 := by omega
      simpa only [finalizeRun, noSpill, dite_false] using storedU.chaining
  · have spill : 56 < value.buffered.val + 1 := by omega
    have nextTwo : read_pc t = base + finalizeOffset + 84#64 := by
      simpa only [one, if_neg] using next
    obtain ⟨firstFuel, u, executionU, liveU, storedU, countU, pcU⟩ :=
      overflow_block s t base value code data owned compression aligned live stored nextTwo count oldCount
    obtain ⟨lastFuel, v, executionV, liveV, storedV, pcV⟩ :=
      last_block s u base value (overflowBuffer value)
        (compressBuffer value.chaining (overflowBuffer value)) value.byteLen
        0 (by decide) code data owned compression aligned liveU storedU pcU countU
    refine ⟨21 + (firstFuel + lastFuel), v, ?_, liveV, ?_, pcV⟩
    · rw [run_plus, execution, run_plus, executionU, executionV]
    · simpa only [finalizeRun, spill, dite_true] using storedV.chaining

/-- The linked ARM finalizer executes through its original RET. Compression is the
only future-run premise; all padding, helper and digest-store executions are proved. -/
theorem finalize_correct (s : ArmState) (base : BitVec 64) (value : StreamState)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + finalizeOffset) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : FinalizeOwned s base value) :
    ∃ fuel, FinalizePost s (run fuel s) value := by
  obtain ⟨fuel, t, execution, live, chaining, next⟩ :=
    finalize_padding s base value code data compression pc error aligned owned
  obtain ⟨returned, bytes, frame⟩ := digest_return s t base (finalizeRun value).chaining
    code (geometry owned) aligned live chaining next
  refine ⟨fuel + 85, ?_⟩
  rw [run_plus, execution]
  exact ⟨returned, bytes, frame⟩

end SszArm.Hash
