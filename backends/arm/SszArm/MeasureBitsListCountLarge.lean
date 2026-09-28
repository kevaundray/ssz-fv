import SszArm.MeasureBitsListCountModel
import SszArm.MeasureHelpersAllocInput

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem Work.after_allocation {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} (work : Work s args schema bits)
    (post : Alloc.ConstructorPost schema.site s t base) : Work t args schema bits := by
  have result := post.registers 19#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  have arena := post.registers 20#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  have stack := post.registers 31#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  have low := post.registers 26#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  have high := post.registers 25#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  have pointer := post.registers 22#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  have payload := post.registers 23#5 (by cases schema <;> simp only [Schema.site] <;> decide)
  refine ⟨result.trans work.result, arena.trans work.arena, stack.trans work.stack,
    low.trans work.low, high.trans work.high, ?_, ?_⟩
  · cases cap : schema.cap with
    | none => trivial
    | some operand => simpa only [cap, pointer, payload] using work.cap
  · cases schema with
    | bounded cap => trivial
    | progressive cap =>
      have flag := post.registers 8#5 (by simp only [Schema.site]; decide)
      simpa only [flag] using work.flag

theorem count_large_post {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} (work : Work s args schema bits)
    (large : (bits.count >>> (64 : Nat)).setWidth 64 ≠ 0#64)
    (post : Alloc.ConstructorPost schema.site s t base) (actual : NatOperand)
    (success : (countCall s args bits).result = .ok actual) :
    CountPost s t args schema bits base actual := by
  have nativeResult := post.result
  rw [work.allocator_outcome, success] at nativeResult
  refine ⟨success, ?_, post.program, post.error, work.after_allocation post,
    ?_, ?_, nativeResult.2.2.2, ?_, ?_, ?_, ?_, ?_, post.vectors⟩
  · cases schema <;>
      simpa only [Schema.site, Alloc.Site.entry, Schema.countExit, large, ↓reduceIte] using nativeResult.1
  · cases schema <;> exact nativeResult.2.1
  · cases schema <;> exact nativeResult.2.2.1
  · simpa only [work.arena, work.allocator_outcome] using post.cursor
  · simpa only [work.arena, Alloc.addressWord, Alloc.capacityWord] using post.header
  · simpa only [work.allocator_outcome] using post.written
  · have frame : Delimited.MemoryFrame (Alloc.writesFor schema.site s) s t := post.frame
    simp only [Alloc.writesFor, work.allocator_outcome, countWrites, work.arena] at frame ⊢
    with_unfolding_all exact frame
  · intro reg member
    apply post.registers reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> cases schema <;>
      simp only [Schema.site] <;> decide

theorem count_large_executes (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.allocateEntry)
    (work : Work s args schema bits)
    (large : (bits.count >>> (64 : Nat)).setWidth 64 ≠ 0#64) :
    ∃ fuel t, run fuel s = t ∧ Alloc.ConstructorPost schema.site s t base := by
  apply Alloc.constructor_executes schema.site s base code error aligned
  · cases schema <;> exact pc
  · have high : r (.GPR 25#5) s ≠ 0#64 := by
      rw [work.high]
      exact large
    cases schema <;> simp only [Schema.site, Alloc.Site.highReg] <;>
      with_unfolding_all exact high
  · exact Helpers.owned_alloc_input owned work.arena

end SszArm.Measure.Bits.List
