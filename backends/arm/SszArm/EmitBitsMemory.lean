import SszArm.EmitBitsStore
import SszArm.EmitBitsWork

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

theorem spill_address {s : ArmState} {args : Args} (stack : r (.GPR 31#5) s = args.bodySP)
    (low : 176 ≤ args.stack.toNat) :
    (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
  rw [stack, Args.bodySP]
  bv_omega

theorem saved_frame {s : ArmState} {args : Args} (size : Nat)
    (stack : r (.GPR 31#5) s = args.bodySP) (low : 176 ≤ args.stack.toNat) :
    MemoryFrame (bodyWrites args size) s (NatCompare.saved s 9#5) := by
  have frame := shifted_frame Path.list s args size stack low
  intro address outside
  simpa [shifted, state_simp_rules] using frame address outside

theorem spill_output {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (owned : Owned s args desc (.bits bits) size) (stack : r (.GPR 31#5) s = args.bodySP) :
    Protected [((r (.GPR 31#5) s - 16#64).toNat, 8)] args.output.toNat args.capacity.toNat := by
  have slot := spill_address stack owned.stackLow
  rcases owned.outputStack with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    have apart := separate (args.stack.toNat - 176, 16) (by simp [stackWrites])
    simp only [Prod.fst, Prod.snd] at apart ⊢
    rw [slot]
    omega

theorem saved_output_read {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (owned : Owned s args desc (.bits bits) size) (stack : r (.GPR 31#5) s = args.bodySP)
    (index : Nat) (inside : index < args.capacity.toNat) :
    widthLoad (NatCompare.saved s 9#5) (args.output.toNat + index) 1 =
      widthLoad s (args.output.toNat + index) 1 := by
  have slot := spill_address stack owned.stackLow
  have stackBound := args.stack.isLt
  have frame := Delimited.store_frame s (r (.GPR 31#5) s - 16#64) 8 (r (.GPR 9#5) s)
    (by rw [slot]; omega)
  apply frame.load _ 1
  · have bound := owned.outputBound; omega
  · exact (spill_output owned stack).subspan index 1 (by omega)

theorem tail_read_byte {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (path : Path) (owned : Owned s args desc (.bits bits) size)
    (work : WorkRegisters s args path bits) (hasTail : bits.count.toNat % 8 ≠ 0) :
    read_mem_bytes 1 (r (.GPR 22#5) s + r (.GPR 23#5) s) (NatCompare.saved s 9#5) =
      bits.bytes[bits.count.toNat / 8]!.toBitVec := by
  have inside : bits.count.toNat / 8 < bits.bytes.size := by
    have sized := (backing_guards bits).2.2 hasTail
    omega
  have bodyFrame := saved_frame size work.stack owned.stackLow
  have frame : MemoryFrame (writesFor args size) s (NatCompare.saved s 9#5) := by
    intro address outside
    exact bodyFrame address (fun span member => outside span (bodyWrites_subset args size span member))
  have source := frame.bytes (read_mem_bytes 8 (args.value + 16#64) s) bits.bytes
    owned.value_at.2.2.1
    (owned.backingOwned ((read_mem_bytes 8 (args.value + 16#64) s).toNat, bits.bytes.size)
      (by simp [backingSpan])) owned.value_at.2.2.2.1
  have observed := Option.some.inj (source (bits.count.toNat / 8) inside)
  have count : r (.GPR 23#5) s = BitVec.ofNat 64 (bits.count.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← work.full, Nat.mod_eq_of_lt (r (.GPR 23#5) s).isLt]
  rw [work.source, count]
  apply BitVec.eq_of_toNat_eq
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, Array.getElem?_eq_getElem inside,
    getElem!_pos, inside] using observed

theorem byteLoaded_frame {s : ArmState} {args : Args} (size : Nat)
    (stack : r (.GPR 31#5) s = args.bodySP) (low : 176 ≤ args.stack.toNat) :
    MemoryFrame (bodyWrites args size) s (byteLoaded s) := by
  intro address outside
  simpa [byteLoaded, state_simp_rules] using saved_frame size stack low address outside

theorem byteStored_frame {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (owned : Owned s args desc (.bits bits) size)
    (output : r (.GPR 20#5) s = args.output) (stack : r (.GPR 31#5) s = args.bodySP)
    (inside : (r (.GPR 23#5) s).toNat < size) :
    MemoryFrame (bodyWrites args size) s (byteStored s) := by
  have position := store_position owned output inside
  have bound := owned.outputBound
  have fitting := owned.fitting
  have nonzero : size ≠ 0 := by omega
  have first := saved_frame size stack owned.stackLow
  have store := Delimited.store_frame (NatCompare.saved s 9#5) (storeAddress s) 1
    ((r (.GPR 8#5) s).setWidth 8) (by rw [position]; omega)
  intro address outside
  have away := outside (args.output.toNat, size) (by simp [bodyWrites, nonzero])
  have tailOutside : ∀ span ∈ [((storeAddress s).toNat, 1)],
      address.toNat < span.1 ∨ span.1 + span.2 ≤ address.toNat := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [Prod.fst, Prod.snd] at away ⊢
    rw [position]
    omega
  have second := store address tailOutside
  simpa [byteStored, storeMemory, state_simp_rules] using second.trans (first address outside)

theorem byteStored_tail {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (owned : Owned s args desc (.bits bits) size) (output : r (.GPR 20#5) s = args.output)
    (inside : (r (.GPR 23#5) s).toNat < size) :
    widthLoad (byteStored s) (args.output.toNat + (r (.GPR 23#5) s).toNat) 1 =
      some ((r (.GPR 8#5) s).setWidth 8).toNat := by
  have fitting := owned.fitting
  have bounded := owned.outputBound
  have position := store_position owned output inside
  have address : BitVec.ofNat 64 (args.output.toNat + (r (.GPR 23#5) s).toNat) = storeAddress s := by
    rw [← position, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [widthLoad, byteStored, storeMemory, state_simp_rules, address]
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 1 _ _ (by rw [position]; omega)]

theorem byteStored_prefix {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (owned : Owned s args desc (.bits bits) size)
    (output : r (.GPR 20#5) s = args.output) (stack : r (.GPR 31#5) s = args.bodySP)
    (inside : (r (.GPR 23#5) s).toNat < size)
    (index : Nat) (before : index < (r (.GPR 23#5) s).toNat) :
    widthLoad (byteStored s) (args.output.toNat + index) 1 = widthLoad s (args.output.toNat + index) 1 := by
  have fitting := owned.fitting
  have bounded := owned.outputBound
  have position := store_position owned output inside
  have frame := Delimited.store_frame (NatCompare.saved s 9#5) (storeAddress s) 1
    ((r (.GPR 8#5) s).setWidth 8) (by rw [position]; omega)
  have apart : Protected [((storeAddress s).toNat, 1)] (args.output.toNat + index) 1 := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [Prod.fst, Prod.snd]
    rw [position]
    omega
  have unchanged := frame.load (args.output.toNat + index) 1 (by omega) apart
  have saved := saved_output_read owned stack index (by omega)
  simpa only [widthLoad, byteStored, storeMemory, state_simp_rules] using unchanged.trans saved

end SszArm.Emit.Bits
