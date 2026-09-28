import SszX86.BitVectorDivisionSuccess
import SszX86.BitVectorErrorsDivision

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The complete frozen BitVector body executes from its physical post-dispatch
entry through the actual RET on every represented Nat and allocator outcome.
Only the original ABI ownership and linked code image are premises. -/
theorem wholeprogram_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    Eventually (step e) (Post s saved length data address capacity used)
      (s, base + Int64.ofNat entry) := by
  change Eventually (step e) (Post s saved length data address capacity used) (s, base + 115)
  apply eventually_trans (step e) _ _ _
    (division_reached e base hc s saved length data address capacity used owned)
  rintro ⟨u, pc⟩ reached
  have returnedPc : pc = base + 157 := by
    simpa only [Int64.ofBitVec_toBitVec] using reached.post.returned.pc
  subst pc
  cases divided : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).result with
  | error reason =>
    exact division_error_post e base hc.body s u saved length data address capacity used owned reached reason divided
  | ok pair =>
    obtain ⟨quotient, remainder⟩ := pair
    exact division_success_post e base hc s u saved length quotient data remainder address capacity used
      owned reached divided

/-- Allocator exhaustion has precisely the shared two-reservation semantics.
Outside that exact resource case, the native observation is pinned SSZ, not an
assumed successful parse or a canonicalized representation. -/
theorem Post.refines {s : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (post : Post s saved length data address capacity used t)
    (owned : Owned s saved length data address capacity used) :
    (SszNative.BitVector.Exhausted length ⟨address.toNat, capacity.toNat, used.toNat⟩ →
      SszNative.BitVector.failureAt (widthLoad t.1.dmem) s.regs.rdi.toNat .scratchExhausted) ∧
    (¬ SszNative.BitVector.Exhausted length ⟨address.toNat, capacity.toNat, used.toNat⟩ →
      SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
        (Ssz.deserialize (.bitVector length.value) data)) := by
  have physical : data.size < 2^64 := by
    rw [owned.data_length]
    exact s.regs.r14.toBitVec.isLt
  have observed := post.erased
  constructor
  · intro exhausted
    have failed := (SszNative.BitVector.run_scratch_iff length data
      ⟨address.toNat, capacity.toNat, used.toNat⟩).2 exhausted
    simpa only [failed] using observed
  · intro available
    rcases SszNative.BitVector.run_refines length data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ physical with refined | failed
    · simpa only [refined] using observed
    · exact False.elim (available ((SszNative.BitVector.run_scratch_iff length data
        ⟨address.toNat, capacity.toNat, used.toNat⟩).1 failed))

/-- End-to-end pinned-SSZ corollary retains the complete native frame, ABI and
allocation observations instead of discarding them during erasure. -/
theorem program_refines (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    Eventually (step e)
      (fun t => Post s saved length data address capacity used t ∧
        (SszNative.BitVector.Exhausted length ⟨address.toNat, capacity.toNat, used.toNat⟩ →
          SszNative.BitVector.failureAt (widthLoad t.1.dmem) s.regs.rdi.toNat .scratchExhausted) ∧
        (¬ SszNative.BitVector.Exhausted length ⟨address.toNat, capacity.toNat, used.toNat⟩ →
          SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
            (Ssz.deserialize (.bitVector length.value) data)))
      (s, base + Int64.ofNat entry) := by
  apply eventually_trans (step e) _ _ _
    (wholeprogram_correct e base hc s saved length data address capacity used owned)
  intro t post
  exact Eventually.done _ ⟨post, post.refines owned⟩

end SszX86.BitVector
