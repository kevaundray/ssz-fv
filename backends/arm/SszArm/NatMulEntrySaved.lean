import SszArm.NatMulEntryInputs
import SszArm.NatMulDispatchFrame

namespace SszArm.NatMul

open Delimited (MemoryFrame Protected)

theorem saved_offset_bound (reg : BitVec 5) (offset : Nat)
    (member : (reg, offset) ∈ savedRegisters) : offset ≤ 88 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | member | member | member | member | member |
    member | member | member | member | member
  all_goals cases member; decide

theorem DispatchFrame.memoryFrame {s t : ArmState} (frame : DispatchFrame s t) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t := by
  intro address outside
  apply frame.memory
  have away := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  omega

theorem Saved.dispatch {entry s t : ArmState} (saved : Saved entry s)
    (stack : 144 ≤ (r (.GPR 31#5) entry).toNat) (frame : DispatchFrame s t) : Saved entry t := by
  have spNat : (r (.GPR 31#5) s).toNat = (r (.GPR 31#5) entry).toNat - 96 := by
    rw [saved.sp]
    bv_omega
  have lower : 16 ≤ (r (.GPR 31#5) s).toNat := by omega
  have upper : (r (.GPR 31#5) s).toNat + 96 ≤ 2^64 := by
    have top := (r (.GPR 31#5) entry).isLt
    omega
  refine ⟨frame.sp.trans saved.sp, ?_,
    (frame.registers 29#5 (by decide)).trans saved.x29, ?_⟩
  · intro reg offset member
    rw [frame.sp, ← saved.words reg offset member]
    have bound := saved_offset_bound reg offset member
    have address : (r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat =
        (r (.GPR 31#5) s).toNat + offset := by bv_omega
    apply frame.memoryFrame.read _ 8
    · rw [address]; omega
    · right
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst span
      right
      rw [address]
      omega
  · intro reg low high
    rw [frame.vectors]
    exact saved.vectors reg low high

end SszArm.NatMul
