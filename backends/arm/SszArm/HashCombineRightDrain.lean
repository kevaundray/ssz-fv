import SszArm.HashCombineActivation
import SszArm.HashCombineCopy

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

theorem Activation.drainContained {origin s : ArmState} (activation : Activation origin s)
    (low : 496 ≤ (r (.GPR 31#5) origin).toNat) :
    ∀ span ∈ drainWrites s, ∃ outer ∈ combineWrites origin,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  intro span member
  obtain ⟨middle, inMiddle, lo, hi⟩ := drain_contained_body s span member
  obtain ⟨outer, inOuter, lower, upper⟩ := activation.contained low middle inMiddle
  exact ⟨outer, inOuter, by omega, by omega⟩

theorem Activation.bufferContained {origin s : ArmState} (activation : Activation origin s)
    (low : 496 ≤ (r (.GPR 31#5) origin).toNat) (bytes : Nat) (bound : bytes ≤ 224) :
    ∀ span ∈ [((r (.GPR 31#5) s).toNat, bytes)], ∃ outer ∈ combineWrites origin,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  obtain ⟨outer, inOuter, lo, hi⟩ := activation.contained low
    ((r (.GPR 31#5) s).toNat, 224) (by simp [bodyWrites])
  exact ⟨outer, inOuter, lo, by omega⟩

@[irreducible] def occupancyStored (s : ArmState) : ArmState := Op.p360.effect s

theorem occupancyStored_local (s : ArmState) (error : read_err s = .None)
    (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) : LocalPost s (occupancyStored s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [occupancyStored, Op.error] using error
  · simpa only [occupancyStored] using Op.program .p360 s
  · simp [occupancyStored, Op.effect, store, next, state_simp_rules]
  · simp [occupancyStored, Op.effect, store, next, state_simp_rules]
  · simp [occupancyStored, Op.effect, store, next, state_simp_rules]
  · intro reg lo hi
    simp [occupancyStored, Op.effect, store, next, state_simp_rules]
  · intro reg lo hi
    simp [occupancyStored, Op.effect, store, next, state_simp_rules]
  · intro address outside
    have apart := outside ((r (.GPR 31#5) s).toNat, 224) (by simp [bodyWrites])
    simp only [occupancyStored, Op.effect, store, next, ArmState.mem_w_eq_mem]
    apply BoolCodec.write_mem_bytes_frame _ _ _ _ address <;> bv_omega

theorem occupancyStored_state (s : ArmState) (value : StreamState)
    (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64)
    (buffer : BytesAt s (r (.GPR 31#5) s) ⟨value.buffer.toArray⟩)
    (words : ChainingAt s (r (.GPR 31#5) s + 64#64) value.chaining)
    (length : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s = value.byteLen.toBitVec)
    (count : (r (.GPR 20#5) s).toNat = value.buffered.val) :
    StateAt (occupancyStored s) (r (.GPR 31#5) s) value := by
  let stored := write_mem_bytes 8 (r (.GPR 31#5) s + 96#64) (r (.GPR 20#5) s) s
  have memory : (occupancyStored s).mem = stored.mem := by
    simp [occupancyStored, Op.effect, store, next, stored, state_simp_rules]
  apply stateAt_mem_eq memory
  have writeFrame := Delimited.store_frame s (r (.GPR 31#5) s + 96#64) 8
    (r (.GPR 20#5) s) (by bv_omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply bytesAt_frame writeFrame _ _ buffer
    · simpa only [Hash.vectorByteArray_size] using (show (r (.GPR 31#5) s).toNat + 64 ≤ 2^64 by omega)
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      left
      simp only [Hash.vectorByteArray_size]
      bv_omega
  · apply words.frame writeFrame (by bv_omega)
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    left
    bv_omega
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ _ _ _ (by bv_omega)]
    have bound := value.buffered.isLt
    bv_omega
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ _ _ _ _ _
      (by bv_omega) (by bv_omega) (by right; bv_omega)]
    exact length

/-- The second direct loop, residual memcpy, and +360 occupancy store. -/
theorem right_drain_correct (origin s : ArmState) (base : BitVec 64)
    (left right : ByteArray) (start : Nat) (startBound : start ≤ right.size)
    (buffer : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (code : CodeAt origin base) (data : DataAt origin base) (compression : CompressionCorrect base)
    (owned : CombineOwned origin base left right) (activation : Activation origin s)
    (pc : read_pc s = if (right.size - start) / 64 = 0 then base + 344#64 else base + 316#64)
    (bufferAt : BytesAt s (r (.GPR 31#5) s) ⟨buffer.toArray⟩)
    (chaining : ChainingAt s (r (.GPR 31#5) s + 64#64) words)
    (lengthAt : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s = byteLen.toBitVec)
    (cursor : r (.GPR 21#5) s = r (.GPR 3#5) origin + BitVec.ofNat 64 start)
    (count : (r (.GPR 20#5) s).toNat = right.size - start) :
    ∃ fuel, let t := run fuel s
      Activation origin t ∧ read_pc t = base + 364#64 ∧
      StateAt t (r (.GPR 31#5) t)
        (SszNative.HashStream.drain buffer words byteLen right start startBound).state := by
  have geometry := activation.physical owned.stackLow
  have directOwned := activation.directOwned owned owned.right owned.rightBound owned.rightOwned chaining
  have included := activation.drainContained owned.stackLow
  obtain ⟨fuel, drained, _, remaining, resultBuffer, resultWords, resultLength⟩ :=
    drain_correct .right s base (r (.GPR 3#5) origin) right start startBound buffer words byteLen
      (activation.code code) (activation.data owned data) compression pc activation.error activation.aligned
      directOwned activation.statePointer (by omega)
      (protected_writes_mono owned.rightOwned (activation.bufferContained owned.stackLow 64 (by decide)))
      (protected_writes_mono owned.initialOwned included)
      (protected_writes_mono owned.roundsOwned included) bufferAt lengthAt cursor count
  let u := run fuel s
  let value := (SszNative.HashStream.drain buffer words byteLen right start startBound).state
  have uActivation := activation.after owned.stackLow drained.local
  have uGeometry := uActivation.physical owned.stackLow
  have uPC : read_pc u = base + 360#64 := drained.pc
  have uCount : (r (.GPR 20#5) u).toNat = value.buffered.val := remaining
  have storedState : StateAt (occupancyStored u) (r (.GPR 31#5) u) value :=
    occupancyStored_state u value (by omega)
      (by simpa only [drained.sp] using resultBuffer)
      (by simpa only [drained.sp] using resultWords)
      (by simpa only [drained.sp] using resultLength) uCount
  have local := occupancyStored_local u uActivation.error (by omega)
  have finalActivation := uActivation.after owned.stackLow local
  refine ⟨fuel + 1, ?_⟩
  rw [run_plus]
  change Activation origin (stepi u) ∧ read_pc (stepi u) = _ ∧ StateAt (stepi u) _ _
  rw [step .p360 u base (uActivation.code code) uActivation.error uActivation.aligned uPC]
  change Activation origin (occupancyStored u) ∧ read_pc (occupancyStored u) = _ ∧
    StateAt (occupancyStored u) (r (.GPR 31#5) (occupancyStored u)) value
  refine ⟨finalActivation, ?_, ?_⟩
  · change r .PC u = _ at uPC
    simp [occupancyStored, Op.effect, store, next, state_simp_rules, uPC, BitVec.add_assoc]
  · simpa only [local.sp] using storedState

end SszArm.Hash.Combine
