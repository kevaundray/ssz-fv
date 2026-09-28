import SszX86.EmitBitsTerminal

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open SszNative (NatOperand)
open UintCodec BoolCodec
open UintCodec.Small (put putF low8 low32 replace8)
open BitVector (constructLow)

theorem remainder64_word (bits : Packed) :
    constructLow bits.count &&& 7#64 = BitVec.ofNat 64 (bits.count.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  have rem := remainder_nat bits
  have small : bits.count.toNat % 8 < 2^64 := by omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using rem

/-- Both native paths reload the original low count, compute its remainder,
and mask a dirty final input byte. The equality guard before this block is
already proved from Packed.sized, not assumed by the body entry contract. -/
theorem tail_mask_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (bits : Packed) (src : BitVec 64) (size : Nat) (list : Bool)
    (copied : Copied s t bits src size list) (nonaligned : bits.count.toNat % 8 ≠ 0)
    (value : t.regs.rax.toBitVec.take 8 = (bits.bytes[bits.count.toNat / 8]!).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ u, Copied s u bits src size list →
      u.regs.rax.toBitVec.take 8 =
        (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2^(bits.count.toNat % 8)-1)).toBitVec →
      u.regs.rsi = t.regs.rsi →
      Eventually (step e) P (u, base + if list then 562 else 789)) :
    Eventually (step e) P (t, base + if list then 543 else 770) := by
  have rem := remainder64_word bits
  have small : bits.count.toNat % 8 < 8 := by omega
  apply tail_count_load e base hc list t (constructLow bits.count)
  · simpa only [copied.stack] using copied.low
  apply tail_remainder_guard e base hc list
  · simp only [remainderLoaded, UInt64.toBitVec_ofBitVec, rem]
    intro zero
    have zeroNat := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bits.count.toNat % 8 < 2^64 by omega)] at zeroNat
    exact nonaligned zeroNat
  intro af
  apply mask_cps e base hc list _ (bits.count.toNat % 8) small
  · simp [tailRemainder, remainderLoaded, rem, low8, UintCodec.Small.get, Reg64s.get64]
  intro flags
  apply next
  · exact copied.of_stable rfl
  · have byteMask := maskByte_eq (bits.bytes[bits.count.toNat / 8]!) (bits.count.toNat % 8) small
    have initial : t.regs.rax.toBitVec.setWidth 8 =
        (bits.bytes[bits.count.toNat / 8]!).toBitVec := by
      simpa only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using value
    simpa [masked, maskByte, tailRemainder, remainderLoaded, putF, put, UintCodec.Small.get, replace8,
      low8, Reg64s.set64, Reg64s.get64, BitVec.replaceLow, BitVec.take,
      initial] using byteMask
  · rfl

theorem vector_suffix (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (length : NatOperand) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s (.bitVector length) bits src size) (copied : Copied s t bits src size false) :
    Eventually (step e) (Post base s (.bitVector length) bits) (t, base + 738) := by
  have full := copied.full_nat owned.physical
  have saved := copied.saved_nat owned.physical
  simp only [Bool.false_eq_true, ↓reduceIte] at saved
  by_cases aligned : bits.count.toNat % 8 = 0
  · have backing := (backing_guards bits).2.1 aligned
    apply vector_aligned e base hc t
    · apply UInt64.toBitVec_inj.mp
      rw [copied.saved, copied.full]
      simp only [Bool.false_eq_true, ↓reduceIte, backing]
    intro flags
    exact vector_aligned_terminal e base hc s _ length bits src size owned
      (copied.of_stable rfl) aligned
  · have backing := (backing_guards bits).2.2 aligned
    have capacityBound := vector_tail_guard owned.valid aligned
    apply vector_partial e base hc t (by omega)
    intro compareFlags
    apply vector_output_guard e base hc
    · simpa only [copied.capacity] using (show t.regs.r13.toNat < s.regs.r9.toNat by omega)
    intro capacityFlags
    let capacityState : MachineData := {{t with status := compareFlags} with status := capacityFlags}
    have capacityCopied : Copied s capacityState bits src size false := copied.of_stable rfl
    apply tail_byte_load e base hc false capacityState (bits.bytes[bits.count.toNat / 8]!)
    · exact capacityCopied.byte_load owned aligned
    apply vector_last_byte e base hc
    · change t.regs.rbp.toBitVec = t.regs.r13.toBitVec + 1
      rw [copied.saved, copied.full]
      simp only [Bool.false_eq_true, ↓reduceIte, backing, BitVec.ofNat_add]
      rfl
    intro lastFlags
    let ready := lastCompared (byteLoaded capacityState (bits.bytes[bits.count.toNat / 8]!)) lastFlags
    have readyCopied : Copied s ready bits src size false := capacityCopied.of_stable rfl
    have byteValue : ready.regs.rax.toBitVec.take 8 =
        (bits.bytes[bits.count.toNat / 8]!).toBitVec := by
      simp [ready, lastCompared, byteLoaded, BitVec.take]
    have run := tail_mask_cps e base hc s ready bits src size false readyCopied aligned byteValue
      (Post base s (.bitVector length) bits) (fun u copiedU byteU _ =>
        vector_terminal e base hc s u length bits src size owned copiedU aligned byteU)
    simpa only [Bool.false_eq_true, ite_false] using run

end SszX86.Emit.Bits
