import SszArm.NatAddInputs

namespace SszArm.NatAdd

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Width and borrow scans touch only lowering spills, so all three original
arena words survive, without requiring used≤capacity. -/
theorem arena_eq_of_scan {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (frame : NatCompare.Frame s t) : arenaOf t = arenaOf s := by
  have pointer := frame.registers 5#5 (by decide)
  have memory := scan_memory frame owned.stackBound
  have bound := owned.arenaBound
  have address8 : (r (.GPR 5#5) s + 8#64).toNat = (r (.GPR 5#5) s).toNat + 8 := by bv_omega
  have address16 : (r (.GPR 5#5) s + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by bv_omega
  have base := memory.read (r (.GPR 5#5) s) 8 (by omega)
    (by simpa only [Nat.add_zero] using owned.arenaLocal.subspan 0 8 (by decide))
  have capacity := memory.read (r (.GPR 5#5) s + 8#64) 8
    (by rw [address8]; omega)
    (by rw [address8]; exact owned.arenaLocal.subspan 8 8 (by decide))
  have used := memory.read (r (.GPR 5#5) s + 16#64) 8
    (by rw [address16]; omega)
    (by rw [address16]; exact owned.arenaLocal.subspan 16 8 (by decide))
  simp only [arenaOf, pointer, base, capacity, used]

theorem outcome_eq_of_scan {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (frame : NatCompare.Frame s t) :
    outcome t left right = outcome s left right := by
  simp only [outcome, arena_eq_of_scan owned frame]

theorem localWrites_eq_of_scan {s t : ArmState} (frame : NatCompare.Frame s t)
    (out : r (.GPR 0#5) t = r (.GPR 0#5) s) : localWrites t = localWrites s := by
  simp only [localWrites, out, frame.sp]

theorem writesFor_eq_of_scan {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (frame : NatCompare.Frame s t)
    (out : r (.GPR 0#5) t = r (.GPR 0#5) s) :
    writesFor t (outcome t left right) = writesFor s (outcome s left right) := by
  simp only [writesFor, outcome_eq_of_scan owned frame,
    localWrites_eq_of_scan frame out, frame.registers 5#5 (by decide)]

/-- Reuse the original physical contract after actual scans. Both original
operand pairs and exact limbs are retained; no new disjointness is assumed. -/
theorem Owned.transport {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (frame : NatCompare.Frame s t)
    (out : r (.GPR 0#5) t = r (.GPR 0#5) s) : Owned t left right := by
  have r1 := frame.registers 1#5 (by decide)
  have r2 := frame.registers 2#5 (by decide)
  have r3 := frame.registers 3#5 (by decide)
  have r4 := frame.registers 4#5 (by decide)
  have r5 := frame.registers 5#5 (by decide)
  have arena := arena_eq_of_scan owned frame
  have result := outcome_eq_of_scan owned frame
  have localEq := localWrites_eq_of_scan frame out
  have writes := writesFor_eq_of_scan owned frame out
  have inputs := scan_preserves_inputs owned frame
  refine ⟨r1.trans owned.leftPointer, r2.trans owned.leftPayload,
    r3.trans owned.rightPointer, r4.trans owned.rightPayload,
    inputs.left.representation, inputs.right.representation, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [out] using owned.outputBound
  · simpa only [frame.sp] using owned.stackBound
  · simpa only [out, frame.sp] using owned.outputStack
  · simpa only [r5] using owned.arenaBound
  · simpa only [arena] using owned.arenaStorage
  · simpa only [arena] using owned.arenaNonnull
  · simpa only [localEq, r5] using owned.arenaLocal
  · intro reservation allocated
    have original : (outcome s left right).allocation = some reservation := by
      simpa only [result] using allocated
    simpa only [localEq, r5, result] using owned.fresh reservation original
  · simpa only [writes] using owned.leftOwned
  · simpa only [writes] using owned.rightOwned

end SszArm.NatAdd
