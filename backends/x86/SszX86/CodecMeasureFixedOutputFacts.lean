import SszX86.CodecMeasureFixedOutputPublish
import SszX86.NatDivisionOutputPreserve

namespace SszX86.CodecMeasureFixed.Output
open SszNative BoolCodec UintCodec Serialize.Publish

theorem some_frame (s : MachineData) (operand : NatOperand) :
    Codec.MemoryFrame s.dmem (someMem s)
      (ResultWrites s.regs.rbx.toBitVec (.ok (some operand))) := by
  intro a outside
  have active : ∀ i < 24, a ≠ s.regs.rbx.toBitVec + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inl ⟨i, hi, equal⟩)
  have status : ∀ i < 4, a ≠ (s.regs.rbx.toBitVec + 64#64) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr ⟨i, hi, equal⟩)
  unfold someMem
  rw [show s.regs.rbx.toBitVec + 64#64 = (s.regs.rbx.toBitVec + 64#64) + BitVec.ofNat 64 0 by simp]
  rw [BoolCodec.store_frame _ _ _ 4 0 4 _ (by decide) status]
  have tag := BoolCodec.store_frame _ s.regs.rbx.toBitVec a 24 0 8 (1 : Int) (by decide) active
  simp only [BitVec.add_zero] at tag
  rw [tag]
  simp (disch := first | assumption | omega | decide) only
    [BoolCodec.store_frame (limit := 24)]

theorem none_frame (s : MachineData) :
    Codec.MemoryFrame s.dmem (noneMem s)
      (ResultWrites s.regs.rbx.toBitVec (.ok none)) := by
  intro a outside
  have active : ∀ i < 8, a ≠ s.regs.rbx.toBitVec + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inl ⟨i, hi, equal⟩)
  have status : ∀ i < 4, a ≠ (s.regs.rbx.toBitVec + 64#64) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr ⟨i, hi, equal⟩)
  unfold noneMem
  rw [show s.regs.rbx.toBitVec + 64#64 = (s.regs.rbx.toBitVec + 64#64) + BitVec.ofNat 64 0 by simp]
  rw [BoolCodec.store_frame _ _ _ 4 0 4 _ (by decide) status]
  simpa only [BitVec.add_zero] using
    BoolCodec.store_frame s.dmem s.regs.rbx.toBitVec a 8 0 8 0 (by decide) active

private theorem observe_word (m : DataMem) (out : BitVec 64) (off n : Nat) (v : Int)
    (loaded : Mem.loadInt m (out + BitVec.ofNat 64 off) n = some v) :
    widthLoad m (out.toNat + off) n = some v.toNat := by
  unfold widthLoad
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, loaded]
  rfl

theorem none_observed (s : MachineData) (bound : s.regs.rbx.toNat + 72 ≤ 2^64) :
    ResultAt (widthLoad (noneMem s)) s.regs.rbx.toNat (.ok none) := by
  have tag : Mem.loadInt (noneMem s) (s.regs.rbx.toBitVec + 0#64) 8 = some 0 := by
    simp (disch := first | assumption | omega | decide)
      [noneMem, local_read (extent := 72), BoolCodec.load_store_same, Int.take]
  have status : Mem.loadInt (noneMem s) (s.regs.rbx.toBitVec + 64#64) 4 = some 0 := by
    simp [noneMem, BoolCodec.load_store_same, Int.take]
  exact ⟨by simpa using observe_word _ _ 0 8 0 tag,
    by simpa using observe_word _ _ 64 4 0 status⟩

private theorem read_after_tag (m : DataMem) (out : BitVec 64) (off n : Nat) (v : Int)
    (bound : out.toNat + 72 ≤ 2^64) (within : off+n ≤ 72) (apart : 8 ≤ off) :
    Mem.loadInt (Mem.storeInt m out 8 v) (out + BitVec.ofNat 64 off) n =
      Mem.loadInt m (out + BitVec.ofNat 64 off) n := by
  simpa only [BitVec.add_zero] using
    local_read m out 72 off n 0 8 v bound within (by decide) (Or.inr apart)

theorem some_observed (s : MachineData) (operand : NatOperand)
    (bound : s.regs.rbx.toNat + 72 ≤ 2^64)
    (pointer : s.regs.r14.toBitVec = operand.pointer)
    (payload : s.regs.r15.toBitVec = operand.payload)
    (borrowed : operand.At (widthLoad s.dmem))
    (apart : ∀ p words, operand = .large p words →
      Body.Apart p.toNat (8*words.length) s.regs.rbx.toNat 68) :
    ResultAt (widthLoad (someMem s)) s.regs.rbx.toNat (.ok (some operand)) := by
  have tag : Mem.loadInt (someMem s) (s.regs.rbx.toBitVec + 0#64) 8 = some 1 := by
    simp (disch := first | assumption | omega | decide)
      [someMem, local_read (extent := 72), BoolCodec.load_store_same, Int.take]
  have ptr : Mem.loadInt (someMem s) (s.regs.rbx.toBitVec + 8#64) 8 =
      some (operand.pointer.toNat : Int) := by
    simp (disch := first | assumption | omega | decide) only
      [someMem, read_after_tag, local_read (extent := 72), pointer, load_store_word]
  have val : Mem.loadInt (someMem s) (s.regs.rbx.toBitVec + 16#64) 8 =
      some (operand.payload.toNat : Int) := by
    simp (disch := first | assumption | omega | decide) only
      [someMem, read_after_tag, local_read (extent := 72), payload, load_store_word]
  have status : Mem.loadInt (someMem s) (s.regs.rbx.toBitVec + 64#64) 4 = some 0 := by
    simp [someMem, BoolCodec.load_store_same, Int.take]
  have frame : ∀ a, (∀ i < 68, a ≠ s.regs.rbx.toBitVec + BitVec.ofNat 64 i) →
      (someMem s).get? a = s.dmem.get? a := by
    intro a outside
    apply some_frame s operand a
    rintro (⟨i, hi, equal⟩ | ⟨i, hi, equal⟩)
    · exact outside i (by omega) equal
    · apply outside (64+i) (by omega)
      simpa only [memmove_addr_add] using equal
  have preserved := NatDivision.result_frame_operand s.dmem (someMem s)
    s.regs.rbx.toBitVec frame (by omega) operand apart borrowed
  refine ⟨?_, ⟨?_, ?_, preserved⟩, ?_⟩
  · simpa using observe_word _ _ 0 8 1 tag
  · simpa using observe_word _ _ 8 8 _ ptr
  · simpa [Nat.add_assoc] using observe_word _ _ 16 8 _ val
  · simpa using observe_word _ _ 64 4 0 status

end SszX86.CodecMeasureFixed.Output
