import SszX86.EmitBitsSpills

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open UintCodec BoolCodec
open BitVector (constructLow constructHigh constructQuotient)

@[simp] private theorem ofNat_word (n : Nat) :
    UInt64.ofNat n = (OfNat.ofNat n : UInt64) := rfl

theorem remainder_word (bits : Packed) :
    (((constructLow bits.count).take 32 &&& 7#32).setWidth 64) =
      BitVec.ofNat 64 (bits.count.toNat % 8) := by
  have rem := remainder32_nat bits
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have taken : (constructLow bits.count).take 32 = (constructLow bits.count).setWidth 32 := by
    simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  rw [taken, rem]

private theorem remainder_register (bits : Packed) :
    UInt64.ofBitVec ((bits.count.setWidth 32).setWidth 64) &&& (7 : UInt64) =
      UInt64.ofNat (bits.count.toNat % 8) := by
  apply UInt64.toBitVec_inj.mp
  change ((bits.count.setWidth 32).setWidth 64 &&& 7#64) =
    BitVec.ofNat 64 (bits.count.toNat % 8)
  simpa [constructLow, BitVec.take, BitVec.setWidth_and] using remainder_word bits

/-- All list-side bounds and original backing loads are discharged before the
real PC498 CALL. The argument is uniform in bounded and progressive descriptors. -/
theorem list_prepared (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (prepared s bits src true flags, base + 498)) :
    Eventually (step e) P (s, base + 428) := by
  have quotient := quotient_nat bits owned.physical
  have fullBound := full_le_size owned.kind owned.valid.success
  have fits := owned.valid.fits
  have backing := (backing_guards bits).1
  have lengthWord : (BitVec.ofNat 64 bits.bytes.size).toNat = bits.bytes.size :=
    Nat.mod_eq_of_lt owned.physical
  apply load_count e base hc true s bits.count owned.low owned.high P
  apply shift_count e base hc true (countLoaded s bits.count) bits.count
  · simp [countLoaded]
  · simp [countLoaded]
  intro shiftFlags
  apply capacity_guard e base hc true
  · simpa [quotientState, countLoaded, quotient, UInt64.toNat_ofBitVec] using
      (show bits.count.toNat / 8 ≤ s.regs.r9.toNat by omega)
  intro capacityFlags
  apply list_length_save e base hc _ (BitVec.ofNat 64 bits.bytes.size)
  · simpa [quotientState, countLoaded, lengthWord] using owned.length
  · simpa [quotientState, countLoaded] using
      owned.stack_load (BitVector.Mapping.Extends.refl _) 8 (by decide)
  apply list_backing_guard e base hc
  · simpa [listLengthSaved, quotientState, countLoaded, quotient,
      UInt64.toNat_ofBitVec, UInt64.toNat_ofNat, Nat.mod_eq_of_lt owned.physical] using backing
  intro backingFlags
  apply list_low_save e base hc
  · simpa [listLengthSaved, quotientState, countLoaded] using
      owned.stack_load (BitVector.Mapping.Extends.store s.dmem
        (s.regs.rsp.toBitVec + 8) 8 (BitVec.ofNat 64 bits.bytes.size).toInt) 16 (by decide)
  apply list_remainder e base hc
  intro remainderFlags
  apply list_copy_ready e base hc _ src
  · have headerRead := owned.header_load (spill_frame s bits true size) 16 (by decide)
    simpa [remainderState, listLowSaved, listLengthSaved, quotientState, countLoaded,
      spillMemory] using headerRead.trans owned.pointer
  simpa [prepared, listCopyReady, remainderState, listLowSaved, listLengthSaved,
    quotientState, countLoaded, spillMemory, remainder_register]
    using next remainderFlags

/-- Fixed vectors copy only floor(count/8); the possible final byte is never
read by memcpy and is handled by the native postcopy path. -/
theorem vector_prepared (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (prepared s bits src false flags, base + 732)) :
    Eventually (step e) P (s, base + 672) := by
  have quotient := quotient_nat bits owned.physical
  have fullBound := full_le_size owned.kind owned.valid.success
  have fits := owned.valid.fits
  have backing := (backing_guards bits).1
  have lengthWord : (BitVec.ofNat 64 bits.bytes.size).toNat = bits.bytes.size :=
    Nat.mod_eq_of_lt owned.physical
  apply load_count e base hc false s bits.count owned.low owned.high P
  apply shift_count e base hc false (countLoaded s bits.count) bits.count
  · simp [countLoaded]
  · simp [countLoaded]
  intro shiftFlags
  apply capacity_guard e base hc false
  · simpa [quotientState, countLoaded, quotient, UInt64.toNat_ofBitVec] using
      (show bits.count.toNat / 8 ≤ s.regs.r9.toNat by omega)
  intro capacityFlags
  apply vector_low_save e base hc
  · simpa [quotientState, countLoaded] using
      owned.stack_load (BitVector.Mapping.Extends.refl _) 8 (by decide)
  apply vector_length_load e base hc _ (BitVec.ofNat 64 bits.bytes.size)
  · have headerRead := owned.header_load (spill_frame s bits false size) 24 (by decide)
    simpa [vectorLowSaved, quotientState, countLoaded, spillMemory, lengthWord]
      using headerRead.trans owned.length
  apply vector_backing_guard e base hc
  · simpa [vectorLowSaved, quotientState, countLoaded, quotient,
      UInt64.toNat_ofBitVec, UInt64.toNat_ofNat, Nat.mod_eq_of_lt owned.physical] using backing
  intro backingFlags
  apply vector_copy_ready e base hc _ src
  · have headerRead := owned.header_load (spill_frame s bits false size) 16 (by decide)
    simpa [vectorLowSaved, quotientState, countLoaded, spillMemory] using headerRead.trans owned.pointer
  simpa [prepared, vectorCopyReady, vectorLowSaved, quotientState, countLoaded,
    spillMemory, UInt64.ofBitVec_ofNat] using next backingFlags

end SszX86.Emit.Bits
