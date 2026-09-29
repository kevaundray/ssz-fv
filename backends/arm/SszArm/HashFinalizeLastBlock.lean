import SszArm.HashFinalizeCalls
import SszArm.HashFinalizeZero
import SszArm.HashFinalizeLength

namespace SszArm.Hash.Finalize

open SszNative.HashStream (finishBuffer compressBuffer)

theorem last_block (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (buf : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (position : Nat) (bound : position ≤ 56)
    (code : CodeAt s base) (data : DataAt s base)
    (owned : FinalizeOwned s base value) (compression : CompressionCorrect base)
    (aligned : CheckSPAlignment s) (live : Live s t) (stored : BufferAt s t buf words byteLen)
    (pc : read_pc t = base + finalizeOffset + 168#64)
    (count : r (.GPR 0#5) t = BitVec.ofNat 64 position) :
    ∃ fuel u, run fuel t = u ∧ Live s u ∧
      BufferAt s u (finishBuffer buf position bound byteLen)
        (compressBuffer words (finishBuffer buf position bound byteLen)) byteLen ∧
      read_pc u = base + finalizeOffset + 216#64 := by
  have g := geometry owned
  have ta := live.toActivation.aligned aligned
  let a := lastZeroCallState t
  have liveA : Live s a := live.sameMemory g (lastZeroCall_scalar t ta)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton]; bv_omega)
    (lastZeroCall_sp t ta) (lastZeroCall_memory t ta)
  have storedA : BufferAt s a buf words byteLen := stored.of_memory (lastZeroCall_memory t ta)
  obtain ⟨pcA, linkA, targetA, zeroA, lengthA⟩ := last_zero_arguments t base ta pc
  have target : r (.GPR 0#5) a = statePtr s + BitVec.ofNat 64 position := by
    simpa only [live.state, count] using targetA
  have length : r (.GPR 2#5) a = BitVec.ofNat 64 (56 - position) := by
    rw [lengthA, count]
    bv_omega
  let zeroFuel := Memset.fuel (56 - position)
  let b := run zeroFuel a
  obtain ⟨liveB, storedB, pcB⟩ := zero_call s a base value buf words byteLen position
    (56 - position) (by omega) code owned liveA storedA pcA target zeroA length
  have pcB' : read_pc b = base + finalizeOffset + 188#64 := pcB.trans linkA
  let cleared := SszNative.HashStream.overwrite buf position (List.replicate (56 - position) 0)
    (by simp only [List.length_replicate]; omega)
  let c := lengthCallState b
  obtain ⟨liveC, storedC, pcC, linkC, stateC, inputC⟩ :=
    length_step s b base value cleared words byteLen owned aligned liveB storedB pcB'
  obtain ⟨fuel, liveU, storedU, pcU⟩ := compression_call s c base value
    (finishBuffer buf position bound byteLen) words byteLen code data owned compression
    aligned liveC storedC pcC stateC inputC
  refine ⟨5 + (zeroFuel + (7 + fuel)), run fuel c, ?_, liveU, storedU, pcU.trans linkC⟩
  rw [run_plus, lastZeroCall_run t base (live.toActivation.code code) live.error ta pc,
    run_plus, run_plus,
    lengthCall_run b base (liveB.toActivation.code code) liveB.error
      (liveB.toActivation.aligned aligned) pcB']

end SszArm.Hash.Finalize
