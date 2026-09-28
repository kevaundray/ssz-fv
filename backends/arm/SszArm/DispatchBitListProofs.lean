import SszArm.DispatchBitListPost

namespace SszArm.DispatchBitList

open UintCodec (widthLoad)
open Dispatch (entered)
open BitList (Variant)

theorem body_pc {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) (pc : read_pc s = base) :
    read_pc (entered s (dispatchKind kind)) = base + BitVec.ofNat 64 kind.entry := by
  have target := Dispatch.entered_pc s base (dispatchKind kind) owned.entry pc
  cases kind <;> simpa only [dispatchKind, Dispatch.Kind.entry, Variant.entry,
    BitList.listEntry, BitList.progressiveEntry] using target

/-- Actual private codec::deserialize PC0, including its six save pairs and
physical descriptor branch tree, through the original LR return. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (kind : Variant)
    (limit : Option Nat) (data : Ssz.Bytes) (owned : Owned s kind limit data)
    (entryCode : Dispatch.CodeAt s base) (bodyCode : BitList.JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t kind limit data := by
  obtain ⟨fuel, t, executed, post⟩ := BitList.program_correct (entered s (dispatchKind kind))
    base kind limit data (body_owned owned) (entered_code kind bodyCode)
    (by simpa only [Dispatch.entered_error] using error)
    (Dispatch.entered_aligned s (dispatchKind kind) aligned) (body_pc owned base pc)
  refine ⟨(dispatchKind kind).steps + fuel, t, ?_, post_of_body owned post⟩
  rw [run_plus, Dispatch.entry_run s base (dispatchKind kind) owned.entry entryCode error aligned pc, executed]

/-- Bounded BitList keeps an arbitrary physical Some(cap) representation and
separates native scratch exhaustion from the pinned SSZ semantic result. -/
theorem bitList_ssz_correct (s : ArmState) (base : BitVec 64) (capacity : Nat) (data : Ssz.Bytes)
    (owned : Owned s .list (some capacity) data)
    (entryCode : Dispatch.CodeAt s base) (bodyCode : BitList.JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t .list (some capacity) data ∧
      (if SszNative.Delimited.Exhausted data (arenaOf s) then
        SszNative.UintCodec.errorAt (widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
      else SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.bitList capacity) data)) := by
  obtain ⟨fuel, t, executed, post, refined⟩ := BitList.bitList_ssz_correct
    (entered s (dispatchKind .list)) base capacity data (body_owned owned) (entered_code .list bodyCode)
    (by simpa only [Dispatch.entered_error] using error)
    (Dispatch.entered_aligned s (dispatchKind .list) aligned) (body_pc owned base pc)
  refine ⟨(dispatchKind .list).steps + fuel, t, ?_, post_of_body owned post, ?_⟩
  · rw [run_plus, Dispatch.entry_run s base (dispatchKind .list) owned.entry entryCode error aligned pc, executed]
  · simpa (config := {decide := true}) only [entered_resources owned, Dispatch.entered_reg] using refined

/-- ProgressiveBitList supports both None and arbitrary represented Some(cap).
The accepted tail helper restores the caller before reusing the old activation. -/
theorem progressiveBitList_ssz_correct (s : ArmState) (base : BitVec 64)
    (limit : Option Nat) (data : Ssz.Bytes) (owned : Owned s .progressive limit data)
    (entryCode : Dispatch.CodeAt s base) (bodyCode : BitList.JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t .progressive limit data ∧
      (if SszNative.Delimited.Exhausted data (arenaOf s) then
        SszNative.UintCodec.errorAt (widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
      else SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.progressiveBitList limit) data)) := by
  obtain ⟨fuel, t, executed, post, refined⟩ := BitList.progressiveBitList_ssz_correct
    (entered s (dispatchKind .progressive)) base limit data (body_owned owned) (entered_code .progressive bodyCode)
    (by simpa only [Dispatch.entered_error] using error)
    (Dispatch.entered_aligned s (dispatchKind .progressive) aligned) (body_pc owned base pc)
  refine ⟨(dispatchKind .progressive).steps + fuel, t, ?_, post_of_body owned post, ?_⟩
  · rw [run_plus, Dispatch.entry_run s base (dispatchKind .progressive) owned.entry entryCode error aligned pc, executed]
  · simpa (config := {decide := true}) only [entered_resources owned, Dispatch.entered_reg] using refined

end SszArm.DispatchBitList
