import SszX86.DispatchBitListOwned
import SszX86.DispatchPost
import SszX86.BitListRefinement

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem bitList_common (s : MachineData) (base : Int64) (tail : Bool) (ra : BitVec 64)
    (limit : Option Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base (listKind tail) ra data address capacity used) (t : MachineState)
    (post : SszX86.BitList.Post (bodyState s base (listKind tail)) (saved s ra)
      tail limit data address capacity used t) :
    CommonPost s base ra address capacity used t := by
  have body := bitList_resources s base tail ra data address capacity used h
  have kept : Preserved s address capacity used t := by
    intro p n region i hi
    have bodyKept := post.preserves_region body p n
      (region.bitList (base := base) (kind := listKind tail) h.stack_low tail) i hi
    rw [body_memory] at bodyKept
    exact bodyKept.trans (region.byte h.stack_low i hi)
  exact ⟨returned_list post.returned, kept, preserved_table h kept⟩

theorem bitList_refines (e : Executable) (base : Int64)
    (code : CodeAt e base) (bodyCode : SszX86.BitList.JointCodeAt e base)
    (s : MachineData) (ra : BitVec 64) (limit : Nat) (pointer payload : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .bitList ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) limit)
    (pointer_load : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payload_load : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (payload.toNat : Int)) :
    Eventually (step e) (fun t =>
      SszX86.BitList.Post (bodyState s base .bitList) (saved s ra) false (some limit)
        data address capacity used t ∧
      CommonPost s base ra address capacity used t ∧
      if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
        SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
      else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
        (Ssz.deserialize (.bitList limit) data)) (s, base) := by
  have body := bitList_owned s base ra limit pointer payload data address capacity used
    h repr pointer_load payload_load
  apply entry_runs e base code s .bitList ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (SszX86.BitList.list_refines e base bodyCode (bodyState s base .bitList) (saved s ra)
      limit pointer payload data address capacity used body)
  intro t post
  refine ⟨post.1, bitList_common s base false ra (some limit) data address capacity used h t post.1, ?_⟩
  simpa only [body_output] using post.2

theorem progressiveBitList_refines (e : Executable) (base : Int64)
    (code : CodeAt e base) (bodyCode : SszX86.BitList.JointCodeAt e base)
    (s : MachineData) (ra : BitVec 64) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : Owned s base .progressiveBitList ra data address capacity used)
    (repr : OptionOwned s address capacity used (s.regs.rsi.toNat + 8) limit) :
    Eventually (step e) (fun t =>
      SszX86.BitList.Post (bodyState s base .progressiveBitList) (saved s ra) true limit
        data address capacity used t ∧
      CommonPost s base ra address capacity used t ∧
      if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
        SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
      else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
        (Ssz.deserialize (.progressiveBitList limit) data)) (s, base) := by
  have body := progressive_owned s base ra limit data address capacity used h repr
  apply entry_runs e base code s .progressiveBitList ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (SszX86.BitList.progressive_refines e base bodyCode (bodyState s base .progressiveBitList)
      (saved s ra) limit data address capacity used body)
  intro t post
  refine ⟨post.1, bitList_common s base true ra limit data address capacity used h t post.1, ?_⟩
  simpa only [body_output] using post.2

end SszX86.Dispatch
