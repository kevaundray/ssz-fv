import SszX86.EmitBitsCopied

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open SszNative (NatOperand)
open UintCodec BoolCodec

abbrev Post (base : Int64) (s : MachineData) (desc : Desc) (bits : Packed)
    (t : MachineState) : Prop :=
  t.2 = base + 1593 ∧ BodyPost s (SszNative.Serialize.emit desc (.bits bits)) t.1

theorem tail_stored_output {s t : MachineData} {bits : Packed} {src : BitVec 64}
    {size : Nat} {list : Bool} (copied : Copied s t bits src size list)
    (physical : bits.bytes.size < 2^64) (byte : UInt8) :
    BytesAt (tailStored t byte).dmem s.regs.r14.toBitVec («prefix» bits ++ #[byte]) := by
  have backing := (backing_guards bits).1
  have bound : («prefix» bits).size < 2^64 := by rw [prefix_size]; omega
  simpa only [tailStored, copied.output, copied.full, prefix_size] using
    bytes_append_store t.dmem s.regs.r14.toBitVec («prefix» bits) byte bound copied.prefix

theorem tail_stored_frame {s t : MachineData} {bits : Packed} {src : BitVec 64}
    {size : Nat} {list : Bool} (copied : Copied s t bits src size list)
    (inside : bits.count.toNat / 8 < size) (byte : UInt8) :
    MemoryFrame s.dmem (tailStored t byte).dmem (BodyWritable s size) := by
  apply frame_trans copied.frame
  apply frame_mono (store_frame t.dmem _ 1 byte.toBitVec.toInt)
  intro a member
  apply Or.inl
  rw [copied.output, copied.full] at member
  exact span_subspan _ _ _ _ (by omega) member

theorem vector_terminal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (length : NatOperand) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s (.bitVector length) bits src size)
    (copied : Copied s t bits src size false)
    (nonaligned : bits.count.toNat % 8 ≠ 0)
    (value : t.regs.rax.toBitVec.take 8 =
      (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2^(bits.count.toNat % 8)-1)).toBitVec) :
    Eventually (step e) (Post base s (.bitVector length) bits) (t, base + 789) := by
  let byte := bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2^(bits.count.toNat % 8)-1)
  have sizeEq := vector_size owned.valid.success
  have backing := (backing_guards bits).2.2 nonaligned
  have inside : bits.count.toNat / 8 < size := by omega
  have encoded : SszNative.Serialize.emit (.bitVector length) (.bits bits) = «prefix» bits ++ #[byte] := by
    simp [SszNative.Serialize.emit, SszNative.PackedBits.canonicalBytes, «prefix», byte, nonaligned]
  have output := tail_stored_output copied owned.physical byte
  have frame := tail_stored_frame copied inside byte
  have emitted := owned.valid.emitted_size
  apply tail_store e base hc false t byte value (copied.tail_load owned inside)
  apply length_store e base hc .vectorPartial (tailStored t byte) size
  · simpa only [LengthSite.word, tailStored, sizeEq, Bool.false_eq_true, ite_false] using copied.saved
  · simpa only [tailStored, copied.result, BitVec.add_zero] using
      Large.mapped_load (tailStored t byte).dmem s.regs.rbx.toBitVec 8 0 8
        (Large.mapped_store _ _ _ _ _ _ (copied.mapping _ _ owned.resultMapped)) (by decide)
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  rw [← emitted]
  apply length_post s (tailStored t byte)
  · simpa only [emitted] using owned.valid.representable
  · exact copied.stack
  · exact copied.result
  · exact copied.vector
  · simpa only [encoded] using output
  · simpa only [emitted] using frame
  · simpa only [emitted] using owned.outputResult

theorem vector_aligned_terminal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (length : NatOperand) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s (.bitVector length) bits src size)
    (copied : Copied s t bits src size false) (aligned : bits.count.toNat % 8 = 0) :
    Eventually (step e) (Post base s (.bitVector length) bits) (t, base + 1275) := by
  have sizeEq := vector_size owned.valid.success
  have encoded : SszNative.Serialize.emit (.bitVector length) (.bits bits) = «prefix» bits := by
    simp [SszNative.Serialize.emit, SszNative.PackedBits.canonicalBytes, «prefix», aligned]
  have emitted := owned.valid.emitted_size
  apply length_store e base hc .vectorAligned t size
  · simpa only [LengthSite.word, sizeEq, Bool.false_eq_true, ite_false] using copied.saved
  · exact copied.result_load owned
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  rw [← emitted]
  apply length_post s t
  · simpa only [emitted] using owned.valid.representable
  · exact copied.stack
  · exact copied.result
  · exact copied.vector
  · simpa only [encoded] using copied.prefix
  · simpa only [emitted] using copied.frame
  · simpa only [emitted] using owned.outputResult

theorem list_terminal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (kind : IsList desc)
    (copied : Copied s t bits src size true)
    (value : t.regs.rdx.toBitVec.take 8 =
      (if bits.count.toNat % 8 = 0 then (1 : UInt8) else
        (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2^(bits.count.toNat % 8)-1)) |||
          (1 <<< UInt8.ofNat (bits.count.toNat % 8))).toBitVec) :
    Eventually (step e) (Post base s desc bits) (t, base + 1169) := by
  let byte : UInt8 := if bits.count.toNat % 8 = 0 then 1 else
    (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2^(bits.count.toNat % 8)-1)) |||
      (1 <<< UInt8.ofNat (bits.count.toNat % 8))
  have sizeEq := list_size kind owned.valid.success
  have inside : bits.count.toNat / 8 < size := by omega
  have encoded : SszNative.Serialize.emit desc (.bits bits) = «prefix» bits ++ #[byte] := by
    cases desc <;> simp_all [IsList, SszNative.Serialize.emit,
      SszNative.PackedBits.delimitedBytes, «prefix», byte]
  have output := tail_stored_output copied owned.physical byte
  have frame := tail_stored_frame copied inside byte
  have emitted := owned.valid.emitted_size
  apply tail_store e base hc true t byte value (copied.tail_load owned inside)
  apply list_increment e base hc
  intro flags
  apply length_store e base hc .list (listIncremented (tailStored t byte) flags) size
  · simp only [LengthSite.word, listIncremented, tailStored, UInt64.toBitVec_add,
      copied.full, sizeEq, BitVec.ofNat_add]
    rfl
  · simpa only [listIncremented, tailStored, copied.result, BitVec.add_zero] using
      Large.mapped_load (tailStored t byte).dmem s.regs.rbx.toBitVec 8 0 8
        (Large.mapped_store _ _ _ _ _ _ (copied.mapping _ _ owned.resultMapped)) (by decide)
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  rw [← emitted]
  apply length_post s (listIncremented (tailStored t byte) flags)
  · simpa only [emitted] using owned.valid.representable
  · exact copied.stack
  · exact copied.result
  · exact copied.vector
  · simpa only [encoded, listIncremented] using output
  · simpa only [emitted, listIncremented] using frame
  · simpa only [emitted] using owned.outputResult

end SszX86.Emit.Bits
