import SszX86.CodecSerializeMeasureOwned

namespace SszX86.CodecSerialize
open SszNative UintCodec

/-- Original entry executes all five native PUSHes and CALL42. The resulting
callee ownership is derived from the original raw recursive input storage. -/
theorem measure_entry (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (desc : SszNative.Codec.Desc) (value : SszNative.Codec.Value)
    (readonly : Codec.Footprint) (address capacity used ra : BitVec 64)
    (owned : Owned s base desc value readonly address capacity used ra) :
    Eventually (step e)
      (fun t => t = (Serialize.measureState s base, base + Int64.ofInt measureOffset) ∧
        CodecMeasure.Owned t.1 (base + Int64.ofInt measureOffset)
          desc value readonly address capacity used (base + 47).toBitVec true)
      (s, base) := by
  apply Serialize.entry_runs e base code.wrapper s
    (owned.stack_window_mapped 144 144 (by decide) (stackBytes_wrapper desc))
  exact .refl _ ⟨rfl, owned.measure_owned⟩

end SszX86.CodecSerialize
