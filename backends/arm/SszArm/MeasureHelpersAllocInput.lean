import SszArm.MeasureBitsAllocModel
import SszArm.MeasureOwnership

namespace SszArm.Measure.Helpers

open SszNative.Serialize (Desc Value)

theorem owned_alloc_input {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (arena : r (.GPR 20#5) s = args.arena) :
    Bits.Alloc.Input s := by
  have header : Bits.Alloc.addressWord s = read_mem_bytes 8 args.arena s := by
    simp only [Bits.Alloc.addressWord, arena]
  have capacity : Bits.Alloc.capacityWord s = read_mem_bytes 8 (args.arena + 8#64) s := by
    simp only [Bits.Alloc.capacityWord, arena]
  have used : Bits.Alloc.usedWord s = read_mem_bytes 8 (args.arena + 16#64) s := by
    simp only [Bits.Alloc.usedWord, arena]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [arena] using owned.arenaBound
  · simpa only [arenaOf, header, capacity] using owned.storageBound
  · simpa only [arenaOf, header, capacity] using owned.nonnull
  · simp only [arena, header, capacity, used]
    rcases owned.freeLocal with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      exact separate _ (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

end SszArm.Measure.Helpers
