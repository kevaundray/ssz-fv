import SszArm.SerializeMeasure

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open Delimited (Span Protected MemoryFrame)
open UintCodec (widthLoad)

/-- Once measurement returns, no wrapper or emitter instruction touches arena
state or committed count limbs. This preserves failures without rolling back. -/
structure Resources (s t : ArmState) (args : Args) (desc : Desc) (value : Value) : Prop where
  cursor : (read_mem_bytes 8 (args.arena + 16#64) t).toNat = (measured s args desc value).used
  header : read_mem_bytes 8 args.arena t = read_mem_bytes 8 args.arena s ∧
    read_mem_bytes 8 (args.arena + 8#64) t = read_mem_bytes 8 (args.arena + 8#64) s
  written : ∀ call ∈ (measured s args desc value).calls, NatDivision.WrittenAt (widthLoad t) call

theorem Measured.resources {s t : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (post : Measured s t base desc value) : Resources s t (Args.ofEntry s) desc value :=
  ⟨post.cursor, post.header, post.written⟩

theorem Resources.of_frame {s t u : ArmState} {args : Args} {desc : Desc} {value : Value}
    {writes : List Span} (owned : Owned s args desc value)
    (resources : Resources s t args desc value) (frame : MemoryFrame writes t u)
    (covered : Covers writes (stackSpans args ++ externalSpans args)) :
    Resources s u args desc value := by
  have headerProtected := protected_of_covers owned.arenaOwned covered
  have r0 := Emit.frame_read_offset frame args.arena 24 0 8 owned.arenaBound headerProtected (by decide)
  have r8 := Emit.frame_read_offset frame args.arena 24 8 8 owned.arenaBound headerProtected (by decide)
  have r16 := Emit.frame_read_offset frame args.arena 24 16 8 owned.arenaBound headerProtected (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨?_, ⟨r0.trans resources.header.1, r8.trans resources.header.2⟩, ?_⟩
  · rw [r16]
    exact resources.cursor
  · intro call member reservation allocated index
    have bounds := (Measure.resource_measure (arenaOf s args) desc value).allocations
      call member reservation allocated
    have count := Measure.callsTwo_measure (arenaOf s args) desc value call member reservation allocated
    have availability : (arenaOf s args).used ≤ (arenaOf s args).capacity := by omega
    have freeProtected : Protected writes (freeSpan s args).1 (freeSpan s args).2 := by
      apply protected_of_covers owned.freeOwned
      intro span inWrites
      obtain ⟨outer, outerMember, lower, upper⟩ := covered span inWrites
      exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩
    have wordProtected : Protected writes (reservation.pointer + 8 * index.val) 8 := by
      have inside : reservation.pointer - (freeSpan s args).1 + 8 * index.val + 8 ≤
          (freeSpan s args).2 := by
        have small := index.isLt
        simp only [freeSpan] at *
        omega
      have piece := freeProtected.subspan
        (reservation.pointer - (freeSpan s args).1 + 8 * index.val) 8 inside
      have offsetEq : (freeSpan s args).1 +
          (reservation.pointer - (freeSpan s args).1 + 8 * index.val) =
          reservation.pointer + 8 * index.val := by
        simp only [freeSpan]
        omega
      simpa only [offsetEq] using piece
    rw [frame.load _ 8 (by have small := index.isLt; have bound := owned.storageBound; omega)
      wordProtected]
    exact resources.written call member reservation allocated index

theorem Measured.plan_status {s t : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (post : Measured s t base desc value) (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand) :
    read_mem_bytes 4 ((Args.ofEntry s).plan + 64#64) t = 0#32 := by
  have result := post.result
  simp only [success, Measure.ResultAt] at result
  apply BitVec.eq_of_toNat_eq
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj result.2.2.2.2

theorem Measured.plan_operand {s t : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (post : Measured s t base desc value) (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand) :
    read_mem_bytes 8 ((Args.ofEntry s).plan + 16#64) t = operand.pointer ∧
    read_mem_bytes 8 ((Args.ofEntry s).plan + 24#64) t = operand.payload ∧
    operand.At (widthLoad t) := by
  have result := post.result
  simp only [success, Measure.ResultAt] at result
  obtain ⟨pointer, payload, input⟩ := result.2.2.1
  refine ⟨?_, ?_, input⟩
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj pointer
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.add_assoc] using Option.some.inj payload

end SszArm.Serialize
