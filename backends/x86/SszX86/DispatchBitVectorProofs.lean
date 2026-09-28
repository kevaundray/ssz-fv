import SszX86.DispatchBitVectorWrites
import SszX86.DispatchPost

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem bitVector_common (s : MachineData) (base : Int64) (ra : BitVec 64)
    (length : NatOperand) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .bitVector ra data address capacity used) (t : MachineState)
    (post : SszX86.BitVector.Post (bodyState s base .bitVector) (saved s ra)
      length data address capacity used t) :
    CommonPost s base ra address capacity used t := by
  have kept : Preserved s address capacity used t := by
    intro p n hp i hi
    have native := hp.bitVector (base := base) (kind := .bitVector) h.stack_low
    have inside : p + i < 2^64 := by have := hp.bound; omega
    have frame : t.1.dmem.get? (BitVec.ofNat 64 (p + i)) =
        (savedMem s).get? (BitVec.ofNat 64 (p + i)) := by
      apply post.frame
      · have apart := native.output
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inside]
        unfold Body.Apart Body.Outside at *
        omega
      · have apart := native.work
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inside]
        unfold Body.Apart Body.Outside at *
        omega
      · have apart := native.cursor
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inside]
        unfold Body.Apart Body.Outside at *
        omega
      · intro span member
        have bounds := bitVector_writes length data address.toNat capacity.toNat used.toNat span member
        have apart := hp.arena
        have usedBound := h.used_bound
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inside]
        unfold Body.Apart Body.Outside at *
        omega
    exact frame.trans (hp.byte h.stack_low i hi)
  exact ⟨returned_body post.returned, kept, preserved_table h kept⟩

theorem bitVector_refines (e : Executable) (base : Int64)
    (dispatchCode : CodeAt e base) (bodyCode : SszX86.BitVector.JointCodeAt e base)
    (s : MachineData) (ra : BitVec 64) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : Owned s base .bitVector ra data address capacity used)
    (repr : NatArithmetic.operandAt (widthLoad s.dmem) (s.regs.rsi.toNat + 8) length)
    (borrowed : OperandOwned s address capacity used length) :
    Eventually (step e) (fun t =>
      SszX86.BitVector.Post (bodyState s base .bitVector) (saved s ra)
        length data address capacity used t ∧
      CommonPost s base ra address capacity used t ∧
      (SszNative.BitVector.Exhausted length ⟨address.toNat, capacity.toNat, used.toNat⟩ →
        SszNative.BitVector.failureAt (widthLoad t.1.dmem) s.regs.rdi.toNat .scratchExhausted) ∧
      (¬ SszNative.BitVector.Exhausted length ⟨address.toNat, capacity.toNat, used.toNat⟩ →
        SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
          (Ssz.deserialize (.bitVector length.value) data))) (s, base) := by
  have body := bitVector_owned s base ra length data address capacity used h repr borrowed
  apply entry_runs e base dispatchCode s .bitVector ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (SszX86.BitVector.program_refines e base bodyCode (bodyState s base .bitVector) (saved s ra)
      length data address capacity used body)
  intro t post
  refine ⟨post.1, bitVector_common s base ra length data address capacity used h t post.1, ?_⟩
  simpa only [body_output] using post.2

end SszX86.Dispatch
