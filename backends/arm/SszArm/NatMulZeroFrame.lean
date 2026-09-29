import SszArm.NatMulEntry
import SszArm.NatMulReturnZero

namespace SszArm.NatMul

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected Returned)

/-- The shared zero branch retains the original cursor, writes no arena words,
and makes no allocation, independently of the raw operand representations. -/
theorem zero_outcome (s : ArmState) (left right : SszNative.NatOperand)
    (zero : left.wordCount = 0 ∨ right.wordCount = 0) :
    outcome s left right =
      SszNative.NatArithmetic.unchanged (arenaOf s).used (.ok (.small 0#64)) :=
  SszNative.NatMul.run_zero left right
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used zero

/-- The return's lowering slot lies inside the original 144-byte frame.
Only the success payload and status bytes are writable outside that frame. -/
theorem zero_return_covered {s u : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (frame : EntryFrame s u)
    (zero : left.wordCount = 0 ∨ right.wordCount = 0) :
    BitVector.Covers (writesFor s (outcome s left right))
      (returnWrites u (r (.GPR 0#5) u)) := by
  have model := zero_outcome s left right zero
  have stack := owned.stackBound
  have sp : (r (.GPR 31#5) u).toNat = (r (.GPR 31#5) s).toNat - 96 := by
    rw [frame.sp]
    bv_omega
  intro span member
  simp only [returnWrites, frame.output, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨((r (.GPR 0#5) s).toNat, 16),
      by simp [writesFor, model, SszNative.NatArithmetic.unchanged, localWrites],
      Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨((r (.GPR 0#5) s).toNat + 64, 4),
      by simp [writesFor, model, SszNative.NatArithmetic.unchanged, localWrites],
      Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨((r (.GPR 31#5) s).toNat - 144, 144),
      by simp [writesFor, model, SszNative.NatArithmetic.unchanged, localWrites], ?_, ?_⟩
    all_goals simp only [Prod.fst, Prod.snd, sp]; omega

/-- Reconstitute the original contract from the real zero-result stores and
its complete frame, retaining both full raw input lists and all arena fields. -/
theorem zero_post (s t : ArmState) (left right : SszNative.NatOperand)
    (owned : Owned s left right) (zero : left.wordCount = 0 ∨ right.wordCount = 0)
    (returned : Returned s t)
    (image : SszNative.NatArithmetic.AddResultAt (widthLoad t)
      (r (.GPR 0#5) s).toNat (.ok (.small 0#64)))
    (frame : MemoryFrame (writesFor s (outcome s left right)) s t) :
    Post s t left right := by
  have model := zero_outcome s left right zero
  have arena : Protected (writesFor s (outcome s left right))
      (r (.GPR 5#5) s).toNat 24 := by
    simpa only [writesFor, model, SszNative.NatArithmetic.unchanged] using owned.arenaLocal
  have physical := owned.arenaBound
  have capAddress : (r (.GPR 5#5) s + 8#64).toNat = (r (.GPR 5#5) s).toNat + 8 := by
    bv_omega
  have usedAddress : (r (.GPR 5#5) s + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by
    bv_omega
  have baseSame := frame.read (r (.GPR 5#5) s) 8 (by omega)
    (by simpa using arena.subspan 0 8 (by decide))
  have capSame := frame.read (r (.GPR 5#5) s + 8#64) 8 (by rw [capAddress]; omega)
    (by rw [capAddress]; exact arena.subspan 8 8 (by decide))
  have usedSame := frame.read (r (.GPR 5#5) s + 16#64) 8 (by rw [usedAddress]; omega)
    (by rw [usedAddress]; exact arena.subspan 16 8 (by decide))
  refine ⟨returned, ?_, ?_, ?_, frame,
    NatAdd.operand_preserved frame left owned.leftAt owned.leftOwned,
    NatAdd.operand_preserved frame right owned.rightAt owned.rightOwned, baseSame, capSame⟩
  · simpa only [model, SszNative.NatArithmetic.unchanged] using image
  · intro reservation allocated
    simp [model, SszNative.NatArithmetic.unchanged] at allocated
  · simp only [model, SszNative.NatArithmetic.unchanged, arenaOf, NatAdd.arenaOf, usedSame]

end SszArm.NatMul
