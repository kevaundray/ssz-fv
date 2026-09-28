import SszArm.MeasureHelpersNative

namespace SszArm.Measure.Helpers.ConstructorFrame

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)
open NatFromU128

theorem checkpoint_returned {s u : ArmState} (reached : Checkpoint s u)
    (body : Body) (error : read_err s = .None) : Delimited.Returned s (body.final u) := by
  have returned := body_returned body u (reached.frame.error.trans error)
  refine ⟨returned.pc.trans (reached.frame.registers 30#5 (by decide)),
    returned.error, returned.sp.trans reached.frame.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply reached.frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    bv_omega
  · intro reg low high
    rw [returned.vectors reg low high, reached.frame.vectors]

theorem checkpoint_frame {s u t : ArmState} (reached : Checkpoint s u)
    (writes : List Span) (frame : MemoryFrame writes u t) : MemoryFrame writes s t := by
  intro address outside
  rw [frame address outside, reached.memory]

theorem success_frame_local {s t : ArmState}
    (frame : MemoryFrame (NatFromU128.successWrites s) s t) :
    MemoryFrame (NatFromU128.localWrites s) s t := by
  intro address outside
  have output := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [NatFromU128.localWrites])
  have stack := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [NatFromU128.localWrites])
  apply frame address
  intro span member
  simp only [NatFromU128.successWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> omega

theorem local_header {s t : ArmState} (owned : NatFromU128.Owned s)
    (frame : MemoryFrame (NatFromU128.localWrites s) s t) (displacement : Nat)
    (within : displacement + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 displacement) t =
      read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 displacement) s := by
  have bound := owned.header
  have address : (r (.GPR 4#5) s + BitVec.ofNat 64 displacement).toNat =
      (r (.GPR 4#5) s).toNat + displacement := by bv_omega
  apply frame.read
  · rw [address]
    omega
  · rw [address]
    exact owned.headerLocal.subspan displacement 8 within

theorem wide_header (s : ArmState) (space : WideSpace s) :
    read_mem_bytes 8 (r (.GPR 4#5) s) (Body.wide.final s) = addressWord s ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) (Body.wide.final s) = capacityWord s := by
  have frame := wide_frame s space
  have headerProtected : Protected (wideWrites s) (r (.GPR 4#5) s).toNat 16 := by
    right
    intro span member
    simp only [wideWrites, NatFromU128.successWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl) | (rfl | rfl)
    all_goals
      have output := space.headerOutput
      have stack := space.headerStack
      have payload := space.payloadHeader
      have lower := space.stack
      omega
  have bound := space.header
  constructor
  · apply frame.read
    · omega
    · simpa only [Nat.add_zero] using headerProtected.subspan 0 8 (by decide)
  · apply frame.read
    · bv_omega
    · have address : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by bv_omega
      rw [address]
      exact headerProtected.subspan 8 8 (by decide)

end SszArm.Measure.Helpers.ConstructorFrame
