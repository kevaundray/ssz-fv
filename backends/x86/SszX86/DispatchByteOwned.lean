import SszX86.DispatchTransport

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

/-- Arbitrary native capacities are transported from the original descriptor,
including their complete noncanonical borrowed representation. -/
theorem byte_owned (s : MachineData) (base : Int64) (kind : Kind) (ra : BitVec 64)
    (limit : Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base kind ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) limit) :
    SszX86.ByteView.Owned (bodyState s base kind) (saved s ra) limit data := by
  refine {
    output := h.tail.output
    savedAt := h.saved_at
    separated := h.tail.separated
    capacity_at := repr.represented h.stack_low
    length := h.length
    source := h.source_view
    source_owned := h.source_owned.byteView
    descriptor := ?_
    borrowed := ?_ }
  · have descriptorRegion := h.descriptor_owned.subrange 0 24 (by split <;> decide)
    simpa only [Nat.add_zero, body_descriptor] using descriptorRegion.byteView (base := base) (kind := kind)
  · intro p words stored
    exact (repr.large_protected h.stack_low p words stored).byteView

end SszX86.Dispatch
