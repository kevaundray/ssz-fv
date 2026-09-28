import SszX86.EmitBitsTail

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open UintCodec BoolCodec
open UintCodec.Small (put putF low8 low32 replace8)

private theorem delimiter_join (byte : UInt8) (remainder : Nat) (small : remainder < 8) :
    (1#8 <<< remainder) ||| (byte &&& UInt8.ofNat (2^remainder-1)).toBitVec =
      ((byte &&& UInt8.ofNat (2^remainder-1)) ||| (1 <<< UInt8.ofNat remainder)).toBitVec := by
  rw [BitVec.or_comm, ← maskByte_eq byte remainder small]
  exact delimiterByte_eq byte remainder small

theorem list_partial_suffix (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (kind : IsList desc)
    (copied : Copied s t bits src size true) (nonaligned : bits.count.toNat % 8 ≠ 0) :
    Eventually (step e) (Post base s desc bits) (t, base + 512) := by
  have full := copied.full_nat owned.physical
  have backing := (backing_guards bits).2.2 nonaligned
  have capacityBound := (list_guards kind owned.valid).1
  have small : bits.count.toNat % 8 < 8 := by omega
  have physicalWord : (BitVec.ofNat 64 bits.bytes.size).toNat = bits.bytes.size :=
    Nat.mod_eq_of_lt owned.physical
  apply list_length_load e base hc t (BitVec.ofNat 64 bits.bytes.size)
  · simpa only [copied.stack, physicalWord] using copied.length rfl
  apply list_partial_guard e base hc
  · simpa only [UInt64.toNat_ofBitVec, physicalWord] using
      (show t.regs.r13.toNat < bits.bytes.size by omega)
  intro backingFlags
  let backingState : MachineData :=
    {t with
      regs := {t.regs with rdx := UInt64.ofBitVec (BitVec.ofNat 64 bits.bytes.size), rsi := t.regs.r15}
      status := backingFlags}
  have backingCopied : Copied s backingState bits src size true := copied.of_stable rfl
  apply tail_byte_load e base hc true backingState (bits.bytes[bits.count.toNat / 8]!)
  · exact backingCopied.byte_load owned nonaligned
  apply list_last_byte e base hc
  · change BitVec.ofNat 64 bits.bytes.size = t.regs.r13.toBitVec + 1
    rw [copied.full, backing, BitVec.ofNat_add]
    rfl
  intro lastFlags
  let ready := lastCompared (byteLoaded backingState (bits.bytes[bits.count.toNat / 8]!)) lastFlags
  have readyCopied : Copied s ready bits src size true := backingCopied.of_stable rfl
  have byteValue : ready.regs.rax.toBitVec.take 8 =
      (bits.bytes[bits.count.toNat / 8]!).toBitVec := by
    simp [ready, lastCompared, byteLoaded, BitVec.take]
  have run := tail_mask_cps e base hc s ready bits src size true readyCopied nonaligned byteValue
    (Post base s desc bits)
  simp only [ite_true] at run
  apply run
  intro u copiedU byteU rsiU
  apply delimiter_cps e base hc u (bits.count.toNat % 8) small
  · simp [low8, low32, UintCodec.Small.get, Reg64s.get64, copiedU.saved]
  intro delimiterFlags
  apply list_output_guard e base hc
  · have fullU := copiedU.full_nat owned.physical
    have capU : u.regs.rsi = s.regs.r9 := rsiU.trans copied.capacity
    simpa [delimited, putF, put, UintCodec.Small.get, replace8, Reg64s.set64, Reg64s.get64, capU] using
      (show u.regs.r13.toNat < s.regs.r9.toNat by omega)
  intro guardFlags
  let finished : MachineData := {delimited u (bits.count.toNat % 8) delimiterFlags with status := guardFlags}
  have finishedCopied : Copied s finished bits src size true := copiedU.of_stable rfl
  apply list_terminal e base hc s finished desc bits src size owned kind finishedCopied
  have joined := delimiter_join (bits.bytes[bits.count.toNat / 8]!) (bits.count.toNat % 8) small
  have maskValue : u.regs.rax.toBitVec.setWidth 8 =
      (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2^(bits.count.toNat % 8)-1)).toBitVec := by
    simpa only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using byteU
  simpa [finished, delimited, putF, put, replace8, UintCodec.Small.get, low8, low32,
    Reg64s.set64, Reg64s.get64, BitVec.replaceLow, BitVec.take,
    BitVec.extractLsb'_append_eq_right (w := 56) (w' := 8), nonaligned, maskValue] using joined

theorem list_aligned_suffix (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (kind : IsList desc)
    (copied : Copied s t bits src size true) (aligned : bits.count.toNat % 8 = 0) :
    Eventually (step e) (Post base s desc bits) (t, base + 1155) := by
  have full := copied.full_nat owned.physical
  have capacityBound := (list_guards kind owned.valid).1
  apply aligned_delimiter e base hc t
  apply list_output_guard e base hc
  · simpa [alignedDelimiter, put, UintCodec.Small.get, replace8, Reg64s.set64, Reg64s.get64, copied.capacity] using
      (show t.regs.r13.toNat < s.regs.r9.toNat by omega)
  intro guardFlags
  let finished : MachineData := {alignedDelimiter t with status := guardFlags}
  have finishedCopied : Copied s finished bits src size true := copied.of_stable rfl
  apply list_terminal e base hc s finished desc bits src size owned kind finishedCopied
  simp [finished, alignedDelimiter, put, UintCodec.Small.get, replace8, Reg64s.set64, Reg64s.get64,
    BitVec.replaceLow, BitVec.take, BitVec.extractLsb'_append_eq_right (w := 56) (w' := 8), aligned]

/-- Empty and aligned lists still execute the mandatory delimiter store.
Nonaligned lists mask dirty padding before inserting that delimiter. -/
theorem list_suffix (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (kind : IsList desc)
    (copied : Copied s t bits src size true) :
    Eventually (step e) (Post base s desc bits) (t, base + 504) := by
  have saved := copied.saved
  simp only [↓reduceIte] at saved
  have small : bits.count.toNat % 8 < 8 := by omega
  apply list_test e base hc t
  intro af
  by_cases aligned : bits.count.toNat % 8 = 0
  · have zero : t.regs.rbp.toBitVec.take 32 = 0#32 := by simp [saved, aligned, BitVec.take]
    simp only [zero, beq_self_eq_true, ↓reduceIte]
    exact list_aligned_suffix e base hc s _ desc bits src size owned kind
      (copied.of_stable rfl) aligned
  · have nonzero : t.regs.rbp.toBitVec.take 32 ≠ 0#32 := by
      rw [saved]
      intro equal
      have equalNat := congrArg BitVec.toNat equal
      simp only [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
        Nat.shiftRight_zero] at equalNat
      omega
    simp only [beq_eq_false_iff_ne.mpr nonzero, Bool.false_eq_true, ↓reduceIte]
    exact list_partial_suffix e base hc s _ desc bits src size owned kind
      (copied.of_stable rfl) aligned

end SszX86.Emit.Bits
