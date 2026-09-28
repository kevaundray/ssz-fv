import SszArm.MeasureAllocationFrame

namespace SszArm.Measure

open SszNative.Serialize (Desc Value)
open Delimited (Protected MemoryFrame)

/-- A committed cursor can only shrink the original free suffix. Invalid cursors
remain permitted: their zero-length suffix imposes no memory observation. -/
theorem Owned.free_after {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (cursor : Nat)
    (monotone : (arenaOf s args).used ≤ cursor) :
    Protected (localWrites args (outcome s args desc value) ++ [(args.arena.toNat, 24)])
      ((arenaOf s args).base + cursor) ((arenaOf s args).capacity - cursor) := by
  by_cases available : cursor < (arenaOf s args).capacity
  · have within : cursor - (arenaOf s args).used + ((arenaOf s args).capacity - cursor) ≤
        (arenaOf s args).capacity - (arenaOf s args).used := by omega
    have smaller := owned.freeLocal.subspan (cursor - (arenaOf s args).used)
      ((arenaOf s args).capacity - cursor) within
    have address : (arenaOf s args).base + (arenaOf s args).used +
        (cursor - (arenaOf s args).used) = (arenaOf s args).base + cursor := by omega
    simpa only [address] using smaller
  · left
    omega

/-- No actual primitive path writes the arena base or capacity. Allocation writes
its cursor only, and each reserved limb interval is disjoint from all24 header bytes. -/
theorem Owned.arena_prefix_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Protected (writesFor args (outcome s args desc value)) args.arena.toNat 16 := by
  right
  intro span member
  simp only [writesFor, List.mem_append] at member
  rcases member with localMember | allocation
  · rcases owned.headerLocal with empty | separate
    · contradiction
    · have apart := separate span localMember
      omega
  · simp only [allocationWrites, List.mem_flatMap] at allocation
    obtain ⟨call, callMember, spanMember⟩ := allocation
    cases allocated : call.allocation with
    | none => simp only [allocated, List.not_mem_nil] at spanMember
    | some reservation =>
      simp only [allocated, List.mem_cons, List.not_mem_nil, or_false] at spanMember
      rcases spanMember with rfl | rfl
      · left
        exact Nat.le_refl _
      · rcases owned.allocation_protected call callMember reservation allocated with empty | separate
        · have count := callsTwo_measure (arenaOf s args) desc value call callMember reservation allocated
          omega
        · have apart := separate (args.arena.toNat, 24)
            (List.mem_append.mpr (Or.inr (by simp)))
          dsimp at apart ⊢
          omega

theorem arena_header_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (writesFor args (outcome s args desc value)) s t) :
    read_mem_bytes 8 args.arena t = read_mem_bytes 8 args.arena s ∧
      read_mem_bytes 8 (args.arena + 8#64) t = read_mem_bytes 8 (args.arena + 8#64) s := by
  have bound : args.arena.toNat + 16 ≤ 2^64 := by have original := owned.arenaBound; omega
  have first := Emit.frame_read_offset frame args.arena 16 0 8 bound
    owned.arena_prefix_protected (by decide)
  have second := Emit.frame_read_offset frame args.arena 16 8 8 bound
    owned.arena_prefix_protected (by decide)
  exact ⟨by simpa only [BitVec.add_zero] using first, second⟩

end SszArm.Measure
