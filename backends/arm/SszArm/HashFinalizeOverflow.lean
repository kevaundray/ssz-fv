import SszArm.HashFinalizeLastBlock
import SszArm.HashFinalizeBranches
import SszArm.HashFinalizeReset

namespace SszArm.Hash.Finalize

open SszNative.HashStream (delimiterBuffer overflowBuffer compressBuffer)

theorem overflow_block (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (code : CodeAt s base) (data : DataAt s base)
    (owned : FinalizeOwned s base value) (compression : CompressionCorrect base)
    (aligned : CheckSPAlignment s) (live : Live s t)
    (stored : BufferAt s t (delimiterBuffer value) value.chaining value.byteLen)
    (pc : read_pc t = base + finalizeOffset + 84#64)
    (count : r (.GPR 0#5) t = BitVec.ofNat 64 (value.buffered.val + 1))
    (oldCount : r (.GPR 8#5) t = BitVec.ofNat 64 value.buffered.val) :
    ∃ fuel u, run fuel t = u ∧ Live s u ∧
      BufferAt s u (overflowBuffer value)
        (compressBuffer value.chaining (overflowBuffer value)) value.byteLen ∧
      r (.GPR 0#5) u = 0#64 ∧
      read_pc u = base + finalizeOffset + 168#64 := by
  have g := geometry owned
  have bounded := value.buffered.isLt
  have ta := live.toActivation.aligned aligned
  let a := overflowGuardState t
  have liveA : Live s a := live.sameMemory g (overflowGuard_scalar t ta)
    (by intro reg lo hi; simp) (overflowGuard_sp t ta) (overflowGuard_memory t ta)
  have storedA := stored.of_memory (overflowGuard_memory t ta)
  have pcA : read_pc a = base + finalizeOffset + 92#64 := by
    rw [overflow_guard_pc t ta (by rw [count]; bv_omega), pc]
    simp [BitVec.add_assoc]
  have countA : r (.GPR 0#5) a = BitVec.ofNat 64 (value.buffered.val + 1) :=
    ((overflowGuard_scalar t ta).registers 0#5 (by simp)).trans count
  have oldCountA : r (.GPR 8#5) a = BitVec.ofNat 64 value.buffered.val :=
    ((overflowGuard_scalar t ta).registers 8#5 (by simp)).trans oldCount
  have alignedA := liveA.toActivation.aligned aligned
  let b := overflowZeroCallState a
  have liveB : Live s b := liveA.sameMemory g (overflowZeroCall_scalar a alignedA)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton]; bv_omega)
    (overflowZeroCall_sp a alignedA) (overflowZeroCall_memory a alignedA)
  have storedB := storedA.of_memory (overflowZeroCall_memory a alignedA)
  obtain ⟨pcB, linkB, targetB, zeroB, lengthB⟩ := overflow_zero_arguments a base alignedA pcA
  have target : r (.GPR 0#5) b = statePtr s + BitVec.ofNat 64 (value.buffered.val + 1) := by
    simpa only [liveA.state, countA] using targetB
  have length : r (.GPR 2#5) b = BitVec.ofNat 64 (63 - value.buffered.val) := by
    rw [lengthB, oldCountA]
    bv_omega
  let zeroFuel := Memset.fuel (63 - value.buffered.val)
  let c := run zeroFuel b
  obtain ⟨liveC, storedC0, pcC0⟩ := zero_call s b base value (delimiterBuffer value)
    value.chaining value.byteLen (value.buffered.val + 1) (63 - value.buffered.val)
    (by omega) code owned liveB storedB pcB target zeroB length
  have remaining : 63 - value.buffered.val = 64 - (value.buffered.val + 1) := by omega
  have storedC : BufferAt s c (overflowBuffer value) value.chaining value.byteLen := by
    simpa only [overflowBuffer, remaining] using storedC0
  have pcC : read_pc c = base + finalizeOffset + 112#64 := pcC0.trans linkB
  have alignedC := liveC.toActivation.aligned aligned
  let d := overflowCompressCallState c
  have liveD : Live s d := liveC.sameMemory g (overflowCompressCall_scalar c alignedC)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton]; bv_omega)
    (overflowCompressCall_sp c alignedC) (overflowCompressCall_memory c alignedC)
  have storedD := storedC.of_memory (overflowCompressCall_memory c alignedC)
  obtain ⟨pcD, linkD, stateD, inputD⟩ := overflow_compress_arguments c base alignedC pcC
  have state : r (.GPR 0#5) d = statePtr s + 64#64 := by simpa only [liveC.state] using stateD
  have input : r (.GPR 1#5) d = statePtr s := by simpa only [liveC.state] using inputD
  obtain ⟨compressFuel, liveE, storedE, pcE0⟩ := compression_call s d base value
    (overflowBuffer value) value.chaining value.byteLen code data owned compression aligned
    liveD storedD pcD state input
  let e := run compressFuel d
  have pcE : read_pc e = base + finalizeOffset + 124#64 := pcE0.trans linkD
  obtain ⟨liveU, storedU, zeroU, pcU⟩ := reset_step s e base value (overflowBuffer value)
    (compressBuffer value.chaining (overflowBuffer value)) value.byteLen owned aligned liveE storedE
  refine ⟨2 + (5 + (zeroFuel + (3 + (compressFuel + 11)))), resetState e,
    ?_, liveU, storedU, zeroU, ?_⟩
  · rw [run_plus, overflowGuard_run t base (live.toActivation.code code) live.error ta pc,
      run_plus, overflowZeroCall_run a base (liveA.toActivation.code code) liveA.error alignedA pcA,
      run_plus, run_plus,
      overflowCompressCall_run c base (liveC.toActivation.code code) liveC.error alignedC pcC,
      run_plus, reset_run e base (liveE.toActivation.code code) liveE.error
        (liveE.toActivation.aligned aligned) pcE]
  · rw [pcU, pcE]
    simp [BitVec.add_assoc]

end SszArm.Hash.Finalize
