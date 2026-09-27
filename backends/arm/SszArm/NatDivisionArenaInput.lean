import SszArm.NatDivisionArenaMemory
import SszArm.NatDivisionBodyMemory

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem local_arena_word {original s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (frame : MemoryFrame (localWrites original) original s)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (offset : Nat) (within : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 21#5) s + BitVec.ofNat 64 offset) s =
      read_mem_bytes 8 (r (.GPR 4#5) original + BitVec.ofNat 64 offset) original := by
  have bound := owned.arenaBound
  have address : (r (.GPR 4#5) original + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 4#5) original).toNat + offset := by bv_omega
  rw [arena]
  apply frame.read
  · rw [address]
    omega
  · rw [address]
    exact owned.arenaLocal.subspan offset 8 within

theorem ArenaFrame.saved_pure {original s t : ArmState}
    (frame : ArenaFrame s t) (memory : t.mem = s.mem) (saved : Saved original s) :
    Saved original t := by
  refine ⟨frame.sp.trans saved.sp, ?_, ?_, ?_⟩
  · intro reg offset member
    rw [frame.sp, Memory.mem_eq_iff_read_mem_bytes_eq.mp memory]
    exact saved.words reg offset member
  · intro reg low high
    have keep : reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      bv_omega
    exact (frame.registers reg keep).trans (saved.high reg low high)
  · intro reg low high
    rw [frame.vectors]
    exact saved.vectors reg low high

theorem ArenaFrame.saved_body {original s t : ArmState} {operand : SszNative.NatOperand}
    (frame : ArenaFrame s t) (owned : Owned original operand)
    (memory : MemoryFrame (bodyWrites original operand) s t) (saved : Saved original s) :
    Saved original t := by
  apply saved.body_preserved owned memory frame.sp
  · intro reg low high
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    bv_omega
  · intro reg low high
    exact congrArg (BitVec.setWidth 64) (frame.vectors reg)

/-- A count-two commit fits exactly inside the original allocation-dependent
body frame; the readonly input and saved activation remain outside it. -/
theorem wide_commit_body_frame {original s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (length : (outcome original operand).written.length = 2)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (frame : MemoryFrame [((r (.GPR 21#5) s + 16#64).toNat, 8), (reservation.pointer, 16)] s t) :
    MemoryFrame (bodyWrites original operand) s t := by
  have bound := owned.arenaBound
  have address : (r (.GPR 21#5) s + 16#64).toNat = (r (.GPR 4#5) original).toNat + 16 := by
    rw [arena]
    bv_omega
  apply frame.weaken
  intro span member
  simp only [List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl <;> simp [bodyWrites, allocated, length, address]

end SszArm.NatDivision
