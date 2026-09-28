import SszX86.DispatchUintOwned
import SszX86.DispatchPost
import SszX86.UintBody

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem uint_refines (e : Executable) (base : Int64)
    (dispatchCode : CodeAt e base) (bodyCode : UintCodec.CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : Owned s base .uint ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) expectedWidth)
    (physical : data.size < 2^63) :
    Eventually (step e) (fun t =>
      Body.Post (bodyState s base .uint) (saved s ra) expectedWidth data address capacity used t ∧
      CommonPost s base ra address capacity used t) (s, base) := by
  have body := uint_owned s base ra expectedWidth data address capacity used h repr physical
  apply entry_runs e base dispatchCode s .uint ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (Body.runs e base bodyCode (bodyState s base .uint) (saved s ra)
      expectedWidth data address capacity used body)
  intro t post
  have kept : Preserved s address capacity used t := by
    intro p n region i hi
    have bodyKept := Body.preserves_region (bodyState s base .uint) (saved s ra) expectedWidth data
      address capacity used body t post p n
      (region.uint (base := base) (kind := .uint) h.stack_low) i hi
    rw [body_memory] at bodyKept
    exact bodyKept.trans (region.byte h.stack_low i hi)
  exact ⟨post, returned_body post.returned, kept, preserved_table h kept⟩

end SszX86.Dispatch
