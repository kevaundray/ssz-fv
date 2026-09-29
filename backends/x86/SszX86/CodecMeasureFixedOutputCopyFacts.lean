import SszX86.CodecMeasureFixedOutputCopyMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec Serialize.Publish

/-- These physical images include all opaque bytes at +68..71. -/
theorem copy344_image (m : DataMem) (out : BitVec 64) (v : Image)
    (bound : out.toNat + 72 ≤ 2^64) : ImageAt (copy344Mem m out v) out v := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [copy344Mem, local_read (extent := 72), load_store_word]

theorem copy455_image (m : DataMem) (out : BitVec 64) (v : Image)
    (bound : out.toNat + 72 ≤ 2^64) : ImageAt (copy455Mem m out v) out v := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [copy455Mem, local_read (extent := 72), load_store_word]

theorem copy607_image (m : DataMem) (out : BitVec 64) (v : Image)
    (bound : out.toNat + 72 ≤ 2^64) : ImageAt (copy607Mem m out v) out v := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [copy607Mem, local_read (extent := 72), load_store_word]

theorem copy344_frame (m : DataMem) (out : BitVec 64) (v : Image)
    (error : SszNative.Serialize.Error) :
    Codec.MemoryFrame m (copy344Mem m out v) (ResultWrites out (.error error)) := by
  intro a outside
  have avoid : ∀ i < 72, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [copy344Mem, BoolCodec.store_frame (limit := 72)]

theorem copy455_frame (m : DataMem) (out : BitVec 64) (v : Image)
    (error : SszNative.Serialize.Error) :
    Codec.MemoryFrame m (copy455Mem m out v) (ResultWrites out (.error error)) := by
  intro a outside
  have avoid : ∀ i < 72, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [copy455Mem, BoolCodec.store_frame (limit := 72)]

theorem copy607_frame (m : DataMem) (out : BitVec 64) (v : Image)
    (error : SszNative.Serialize.Error) :
    Codec.MemoryFrame m (copy607Mem m out v) (ResultWrites out (.error error)) := by
  intro a outside
  have avoid : ∀ i < 72, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [copy607Mem, BoolCodec.store_frame (limit := 72)]

end SszX86.CodecMeasureFixed.Output
