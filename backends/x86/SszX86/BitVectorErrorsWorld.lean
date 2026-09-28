import SszX86.BitVectorErrorsReads
import SszX86.BitVectorReached

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The suffix's physical premises are projected from a reached world, not
assumed for any future helper execution. -/
theorem error_suffix_at {s u : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed : BitVec 64}
    {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved) : ErrorSuffixAt s u saved := by
  refine ⟨original, anchors.stack, world.physical.saved_at,
    world.physical.output_bound, world.physical.output_mapped,
    world.physical.stack_low, world.physical.stack_bound,
    world.physical.output_work, world.physical.output_saved, ?_⟩
  simpa only [anchors.stack] using anchors.outputCache

end SszX86.BitVector
