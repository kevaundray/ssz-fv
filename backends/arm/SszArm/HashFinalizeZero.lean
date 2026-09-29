import SszArm.HashFinalizeCompression
import SszArm.HashBufferMemory

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)
open SszNative.HashStream (overwrite)

theorem zero_call (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (buf : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (offset count : Nat) (within : offset + count ≤ 64)
    (code : CodeAt s base) (owned : FinalizeOwned s base value)
    (live : Live s t) (stored : BufferAt s t buf words byteLen)
    (pc : read_pc t = base + memsetOffset)
    (target : r (.GPR 0#5) t = statePtr s + BitVec.ofNat 64 offset)
    (zero : r (.GPR 1#5) t = 0#64)
    (length : r (.GPR 2#5) t = BitVec.ofNat 64 count) :
    let fuel := Memset.fuel count
    Live s (run fuel t) ∧
      BufferAt s (run fuel t)
        (overwrite buf offset (List.replicate count 0) (by simpa using within)) words byteLen ∧
      read_pc (run fuel t) = r (.GPR 30#5) t := by
  dsimp only
  have g := geometry owned
  have physical := g.stateBound
  have targetNat : (statePtr s + BitVec.ofNat 64 offset).toNat =
      (statePtr s).toNat + offset := by bv_omega
  have countNat : (BitVec.ofNat 64 count).toNat = count := by bv_omega
  have at64 : (statePtr s + 64#64).toNat = (statePtr s).toNat + 64 := by bv_omega
  have at104 : (statePtr s + 104#64).toNat = (statePtr s).toNat + 104 := by bv_omega
  have h := memset_correct t base (live.toActivation.code code) pc live.error (by
    rw [target, length, targetNat, countNat]
    omega)
  simp only [target, zero, length, countNat, show (0#64).setWidth 8 = 0#8 from rfl] at h
  arm_word_nf at h
  rcases h with ⟨returned, memory, frame⟩
  let writes : List Span := [((statePtr s + BitVec.ofNat 64 offset).toNat, count)]
  have contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    exact g.state_subspan _ count (by rw [targetNat]; omega) (by rw [targetNat]; omega)
  have savedOwned : Protected writes (bodySP s).toNat 32 := by
    apply g.saved_protected
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right; left
    simp only [targetNat]
    constructor <;> omega
  have chainOwned : Protected writes (statePtr s + 64#64).toNat 32 := by
    right
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right
    simp only [at64, targetNat]
    omega
  have lengthOwned : Protected writes (statePtr s + 104#64).toNat 8 := by
    right
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right
    simp only [at104, targetNat]
    omega
  refine ⟨live.returned g returned frame contained savedOwned, ?_, returned.pc⟩
  constructor
  · exact bytesAt_zero (statePtr s) buf offset count within (by omega) stored.buffer memory
  · exact stored.chaining.frame frame (by rw [at64]; omega) chainOwned
  · rw [read_frame _ 8 frame (by rw [at104]; omega) lengthOwned]
    exact stored.length

end SszArm.Hash.Finalize
