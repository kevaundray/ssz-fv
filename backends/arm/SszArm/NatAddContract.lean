import SszArm.NatAddMemory

namespace SszArm.NatAdd

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Physical caller obligations only. The operands may overlap each other and
already-used arena storage. Neither a valid initial cursor nor a signed capacity
bound is required; the frozen native reservation checks decide exhaustion. -/
structure Owned (s : ArmState) (left right : SszNative.NatOperand) : Prop where
  leftPointer : r (.GPR 1#5) s = left.pointer
  leftPayload : r (.GPR 2#5) s = left.payload
  rightPointer : r (.GPR 3#5) s = right.pointer
  rightPayload : r (.GPR 4#5) s = right.payload
  leftAt : left.At (widthLoad s)
  rightAt : right.At (widthLoad s)
  outputBound : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  stackBound : 16 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
    (r (.GPR 0#5) s).toNat 68
  arenaBound : (r (.GPR 5#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s) (r (.GPR 5#5) s).toNat 24
  fresh : ∀ reservation, (outcome s left right).allocation = some reservation →
    Protected (localWrites s ++ [((r (.GPR 5#5) s).toNat, 24)])
      reservation.pointer (8 * (outcome s left right).written.length)
  leftOwned : OperandOwned (writesFor s (outcome s left right)) left
  rightOwned : OperandOwned (writesFor s (outcome s left right)) right

structure InputsPreserved (s t : ArmState) (left right : SszNative.NatOperand) : Prop where
  left : OperandPreserved s t left
  right : OperandPreserved s t right

theorem inputs_preserved {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right)
    (frame : MemoryFrame (writesFor s (outcome s left right)) s t) :
    InputsPreserved s t left right :=
  ⟨operand_preserved frame left owned.leftAt owned.leftOwned,
   operand_preserved frame right owned.rightAt owned.rightOwned⟩

/-- Observe the original descriptor address: X5 itself is caller-saved. -/
structure ArenaPreserved (s t : ArmState) : Prop where
  base : read_mem_bytes 8 (r (.GPR 5#5) s) t = read_mem_bytes 8 (r (.GPR 5#5) s) s
  capacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s

/-- Cursor writes stop exactly after the immutable base/capacity prefix. -/
theorem Owned.arena_header {s : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) :
    Protected (writesFor s (outcome s left right)) (r (.GPR 5#5) s).toNat 16 := by
  cases allocated : (outcome s left right).allocation with
  | none =>
    have header := owned.arenaLocal.subspan 0 16 (by decide)
    simpa only [writesFor, allocated, Nat.add_zero] using header
  | some reservation =>
    have length := (SszNative.NatAdd.allocation_geometry left right
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used reservation allocated).2.2.2
    have positive : 0 < (outcome s left right).written.length := by
      change (outcome s left right).written.length = _ at length
      split at length <;> omega
    have separateFresh : ∀ span ∈ localWrites s ++ [((r (.GPR 5#5) s).toNat, 24)],
        reservation.pointer + 8 * (outcome s left right).written.length ≤ span.1 ∨
          span.1 + span.2 ≤ reservation.pointer := by
      rcases owned.fresh reservation allocated with empty | separate
      · omega
      · exact separate
    right
    intro span member
    simp only [writesFor, allocated, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with memberLocal | cursor | written
    · rcases owned.arenaLocal with empty | separate
      · omega
      · have apart := separate span memberLocal
        omega
    · subst span
      simp only [Prod.fst, Prod.snd]
      omega
    · have apart := separateFresh ((r (.GPR 5#5) s).toNat, 24) (by simp)
      subst span
      simp only [Prod.fst, Prod.snd] at *
      omega

theorem arena_preserved {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right)
    (frame : MemoryFrame (writesFor s (outcome s left right)) s t) :
    ArenaPreserved s t := by
  have bound := owned.arenaBound
  have header := owned.arena_header
  have capacityAddress : (r (.GPR 5#5) s + 8#64).toNat =
      (r (.GPR 5#5) s).toNat + 8 := by bv_omega
  refine ⟨frame.read _ 8 (by omega) ?_, frame.read _ 8 ?_ ?_⟩
  · simpa only [Nat.add_zero] using header.subspan 0 8 (by decide)
  · rw [capacityAddress]
    omega
  · rw [capacityAddress]
    exact header.subspan 8 8 (by decide)

/-- Exact physical refinement target. Success and failure use the frozen private
arithmetic Result layout, including its 32-bit status at output+64. -/
structure Post (s t : ArmState) (left right : SszNative.NatOperand) : Prop where
  returned : Returned s t
  result : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (outcome s left right).result
  written : WrittenAt (widthLoad t) (outcome s left right)
  cursor : (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t).toNat =
    (outcome s left right).used
  frame : MemoryFrame (writesFor s (outcome s left right)) s t
  inputs : InputsPreserved s t left right
  arena : ArenaPreserved s t

/-- Preservation is derived from the actual byte frame and static ownership;
no execution-equivalent condition is hidden in the caller obligations. -/
theorem post_of_frame (s t : ArmState) (left right : SszNative.NatOperand)
    (owned : Owned s left right) (returned : Returned s t)
    (result : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (outcome s left right).result)
    (written : WrittenAt (widthLoad t) (outcome s left right))
    (cursor : (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t).toNat =
      (outcome s left right).used)
    (frame : MemoryFrame (writesFor s (outcome s left right)) s t) :
    Post s t left right :=
  ⟨returned, result, written, cursor, frame, inputs_preserved owned frame,
   arena_preserved owned frame⟩

/-- A successful physical result denotes unbounded natural addition. The exact
returned pointer/payload and zero status remain part of the conclusion. -/
theorem Post.arithmetic {s t : ArmState} {left right result : SszNative.NatOperand}
    (post : Post s t left right) (success : (outcome s left right).result = .ok result) :
    SszNative.NatArithmetic.operandAt (widthLoad t) (r (.GPR 0#5) s).toNat result ∧
      widthLoad t ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 ∧
      result.value = left.value + right.value := by
  have stored := post.result
  rw [success] at stored
  exact ⟨stored.1, stored.2, SszNative.NatAdd.run_value left right
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used result success⟩

end SszArm.NatAdd
