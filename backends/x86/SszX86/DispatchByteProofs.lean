import SszX86.DispatchByteOwned
import SszX86.DispatchPost

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem byte_common (s : MachineData) (base : Int64) (kind : Kind) (ra : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base kind ra data address capacity used)
    (result : Except Ssz.Err Ssz.Value) (t : MachineState)
    (post : SszX86.ByteView.Post (bodyState s base kind) (saved s ra) result t) :
    CommonPost s base ra address capacity used t := by
  have kept : Preserved s address capacity used t := by
    intro p n region i hi
    have bodyKept := SszX86.ByteView.preserves_region (bodyState s base kind) (saved s ra)
      result t post p n (region.byteView (base := base) (kind := kind)) i hi
    rw [body_memory] at bodyKept
    exact bodyKept.trans (region.byte h.stack_low i hi)
  exact ⟨returned_body post.returned, kept, preserved_table h kept⟩

theorem byteVector_refines (e : Executable) (base : Int64)
    (code : CodeAt e base) (bodyCode : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (limit : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : Owned s base .byteVector ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) limit) :
    Eventually (step e) (fun t =>
      SszX86.ByteView.Post (bodyState s base .byteVector) (saved s ra)
        (Ssz.deserialize (.byteVector limit) data) t ∧
      CommonPost s base ra address capacity used t) (s, base) := by
  apply entry_runs e base code s .byteVector ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (SszX86.ByteView.vector_runs e base bodyCode (bodyState s base .byteVector)
      (saved s ra) limit data (byte_owned s base .byteVector ra limit data address capacity used h repr))
  intro t post
  exact ⟨post, byte_common s base .byteVector ra data address capacity used h _ t post⟩

theorem byteList_refines (e : Executable) (base : Int64)
    (code : CodeAt e base) (bodyCode : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (limit : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : Owned s base .byteList ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) limit) :
    Eventually (step e) (fun t =>
      SszX86.ByteView.Post (bodyState s base .byteList) (saved s ra)
        (Ssz.deserialize (.byteList limit) data) t ∧
      CommonPost s base ra address capacity used t) (s, base) := by
  apply entry_runs e base code s .byteList ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (SszX86.ByteView.list_runs e base bodyCode (bodyState s base .byteList)
      (saved s ra) limit data (byte_owned s base .byteList ra limit data address capacity used h repr))
  intro t post
  exact ⟨post, byte_common s base .byteList ra data address capacity used h _ t post⟩

end SszX86.Dispatch
