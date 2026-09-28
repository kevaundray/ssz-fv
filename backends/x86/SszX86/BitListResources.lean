import SszX86.BitListRefinement

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

/-- Even a zero-bit successful result retains the original borrowed pointer. -/
theorem Post.borrowed_original {s : MachineData} {saved : Saved} {tail : Bool}
    {limit : Option Nat} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (owned : Owned s saved tail data address capacity used)
    (post : Post s saved tail limit data address capacity used t)
    (view : SszNative.Delimited.Borrowed)
    (success : (SszNative.Delimited.run limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩).result = .ok view) :
    widthLoad t.1.dmem (s.regs.rdi.toNat + 32) 8 = some s.regs.rdx.toNat := by
  have physical : data.size < 2^64 := by rw [owned.length]; exact s.regs.r14.toBitVec.isLt
  have shape := SszNative.Delimited.run_success_shape limit data
    ⟨address.toNat, capacity.toNat, used.toNat⟩ physical view success
  have observed := post.observed
  simp only [SszNative.Delimited.ResultAt, success] at observed
  simpa only [shape.1, Nat.add_zero] using observed.2.2.1

/-- Count limbs remain fully committed even on an over-limit semantic error. -/
theorem Post.committed_words {s : MachineData} {saved : Saved} {tail : Bool}
    {limit : Option Nat} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (post : Post s saved tail limit data address capacity used t)
    (ready : SszNative.Delimited.Prepared) (r : SszNative.Arena.Reservation)
    (prepared : (SszNative.Delimited.run limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩).prepared = some ready)
    (allocated : ready.allocation = some r) :
    widthLoad t.1.dmem r.pointer 8 = some ready.count.low.toNat ∧
    widthLoad t.1.dmem (r.pointer + 8) 8 = some ready.count.high.toNat := by
  simpa only [SszNative.Delimited.PreparedAt, allocated] using post.prepared ready prepared

/-- A committed reservation fixes the final cursor, independently of success
or bound rejection; there is no rollback branch hidden by the SSZ erasure. -/
theorem Post.no_rollback {s : MachineData} {saved : Saved} {tail : Bool}
    {limit : Option Nat} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (owned : Owned s saved tail data address capacity used)
    (post : Post s saved tail limit data address capacity used t)
    (r : SszNative.Arena.Reservation)
    (allocated : (SszNative.Delimited.run limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation = some r) :
    widthLoad t.1.dmem (s.regs.rbx.toNat + 16) 8 = some r.used := by
  have physical : data.size < 2^64 := by rw [owned.length]; exact s.regs.r14.toBitVec.isLt
  have resources := SszNative.Delimited.run_resources limit data
    ⟨address.toNat, capacity.toNat, used.toNat⟩ physical
  rw [resources.1] at allocated
  simpa only [resources.2, allocated] using post.cursor

end SszX86.BitList
