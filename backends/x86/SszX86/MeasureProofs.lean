import SszX86.MeasureBodies
import SszX86.MeasureEntry
import SszX86.MeasureObservations
import SszX86.MeasurePadding
import SszX86.MeasureBorrowed

namespace SszX86.Measure
open SszNative SszNative.Serialize

/-- The actual private codec::measure entry through its original caller RET,
for all seven primitive descriptors and either retain flag. Every premise is
original ownership or an exact linked image contract, not a future execution,
comparison outcome, allocation result, or semantic-success assumption. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (s, base) := by
  apply eventually_trans (step e) _ _ _
    (entry_runs e base hc s desc value buffer address capacity used ra retain owned)
  rintro ⟨body, pc⟩ ⟨entryPC, anchors, tag⟩
  dsimp only at entryPC
  subst pc
  apply eventually_trans (step e) _ _ _
    (bodies_run e base hc helpers s body desc value buffer address capacity used ra retain
      owned anchors tag)
  rintro ⟨final, pc⟩ ⟨publishedPC, post⟩
  dsimp only at publishedPC
  subst pc
  exact finish_cps e base hc s body final desc value buffer address capacity used ra retain
    owned anchors tag post

/-- Exact result storage, allocator state, ABI and byte frames accompany the
accepted resource-sensitive refinement of the pinned serializer. Wrong-kind
Seq/Union values receive WrongType and the outside-writes frame; their native
payload/tree ownership is deliberately not asserted by the primitive projection. -/
theorem program_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    Eventually (step e) (fun final =>
      Post s desc value buffer address capacity used ra final ∧
      Measures (Serialize.measure desc value (arenaState address capacity used)).result
        ((Ssz.serialize desc.erase value.erase).map Array.size)) (s, base) := by
  apply eventually_weaken (step e) _ _ _ _
    (program_correct e base hc helpers s desc value buffer address capacity used ra retain owned)
  intro final post
  exact ⟨post, outcome_refines_pinned desc value (arenaState address capacity used) owned.physical⟩

end SszX86.Measure
