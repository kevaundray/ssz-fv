import SszArm.NatDivisionMemory

namespace SszArm.NatDivision

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Physical caller obligations for the native divisor-at-least-two entry path.
The original operand may overlap readonly arena bytes, including its used
prefix. There is no used/capacity invariant or signed capacity restriction;
the frozen reservation checks decide allocation success or exhaustion. -/
structure Owned (s : ArmState) (operand : SszNative.NatOperand) : Prop where
  operandPointer : r (.GPR 1#5) s = operand.pointer
  operandPayload : r (.GPR 2#5) s = operand.payload
  operandAt : operand.At (widthLoad s)
  divisor : 2 ≤ (r (.GPR 3#5) s).toNat
  outputBound : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  stackBound : 80 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 80, 80)]
    (r (.GPR 0#5) s).toNat 68
  arenaBound : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s) (r (.GPR 4#5) s).toNat 24
  fresh : ∀ reservation, (outcome s operand).allocation = some reservation →
    Protected (localWrites s ++ [((r (.GPR 4#5) s).toNat, 24)])
      reservation.pointer (8 * (outcome s operand).written.length)
  operandOwned : OperandOwned (writesFor s (outcome s operand)) operand

theorem Owned.divisor_nonzero {s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand) : r (.GPR 3#5) s ≠ 0#64 := by
  have lower := owned.divisor
  intro zero
  rw [zero] at lower
  simp at lower

theorem Owned.divisor_ne_one {s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand) : r (.GPR 3#5) s ≠ 1#64 := by
  have lower := owned.divisor
  intro one
  rw [one] at lower
  simp at lower

theorem input_preserved {s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand)
    (frame : MemoryFrame (writesFor s (outcome s operand)) s t) :
    OperandPreserved s t operand :=
  operand_preserved frame operand owned.operandAt owned.operandOwned

/-- The descriptor is observed at its original address, because X4 is volatile.
Only its cursor may change; both immutable words and every header byte remain. -/
structure ArenaPreserved (s t : ArmState) : Prop where
  base : read_mem_bytes 8 (r (.GPR 4#5) s) t = read_mem_bytes 8 (r (.GPR 4#5) s) s
  capacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
  bytes : ∀ a : BitVec 64, (r (.GPR 4#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 4#5) s).toNat + 16 → t.mem a = s.mem a

/-- The permitted cursor write begins immediately after the immutable header. -/
theorem Owned.arena_header {s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand) :
    Protected (writesFor s (outcome s operand)) (r (.GPR 4#5) s).toNat 16 := by
  cases allocated : (outcome s operand).allocation with
  | none =>
    have header := owned.arenaLocal.subspan 0 16 (by decide)
    simpa only [writesFor, allocated, Nat.add_zero] using header
  | some reservation =>
    have length := (SszNative.NatDivision.allocation_resources operand (r (.GPR 3#5) s)
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used reservation allocated).2.1
    have positive : 0 < (outcome s operand).written.length := by
      change (outcome s operand).written.length = _ at length
      split at length <;> omega
    have separateFresh : ∀ span ∈ localWrites s ++ [((r (.GPR 4#5) s).toNat, 24)],
        reservation.pointer + 8 * (outcome s operand).written.length ≤ span.1 ∨
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
      omega
    · have apart := separateFresh ((r (.GPR 4#5) s).toNat, 24) (by simp)
      subst span
      simp only [Prod.fst, Prod.snd] at *
      omega

theorem arena_preserved {s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand)
    (frame : MemoryFrame (writesFor s (outcome s operand)) s t) :
    ArenaPreserved s t := by
  have bound := owned.arenaBound
  have header := owned.arena_header
  have capacityAddress : (r (.GPR 4#5) s + 8#64).toNat =
      (r (.GPR 4#5) s).toNat + 8 := by bv_omega
  refine ⟨frame.read _ 8 (by omega) ?_, frame.read _ 8 ?_ ?_, ?_⟩
  · simpa only [Nat.add_zero] using header.subspan 0 8 (by decide)
  · rw [capacityAddress]
    omega
  · rw [capacityAddress]
    exact header.subspan 8 8 (by decide)
  · intro a low high
    exact frame.protected_byte header a low high

/-- Exact refinement to the shared private division Result layout, including
its remainder at output+16 and 32-bit status at output+64. The physical frame
retains the original input bytes and excludes unwritten arena padding. -/
structure Post (s t : ArmState) (operand : SszNative.NatOperand) : Prop where
  returned : Returned s t
  result : SszNative.NatArithmetic.DivisionResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (outcome s operand).result
  written : WrittenAt (widthLoad t) (outcome s operand)
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
    (outcome s operand).used
  frame : MemoryFrame (writesFor s (outcome s operand)) s t
  input : OperandPreserved s t operand
  arena : ArenaPreserved s t

/-- Original-byte preservation follows from the proved ISA frame and static
ownership, never from an execution-equivalent caller hypothesis. -/
theorem post_of_frame (s t : ArmState) (operand : SszNative.NatOperand)
    (owned : Owned s operand) (returned : Returned s t)
    (result : SszNative.NatArithmetic.DivisionResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (outcome s operand).result)
    (written : WrittenAt (widthLoad t) (outcome s operand))
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
      (outcome s operand).used)
    (frame : MemoryFrame (writesFor s (outcome s operand)) s t) :
    Post s t operand :=
  ⟨returned, result, written, cursor, frame, input_preserved owned frame,
   arena_preserved owned frame⟩

/-- A successful physical result is unbounded natural division, with the exact
quotient representation, stored remainder, zero status, and strict remainder
bound. No canonical-input or value-size assumption is needed. -/
theorem Post.arithmetic {s t : ArmState} {operand quotient : SszNative.NatOperand}
    {remainder : BitVec 64} (post : Post s t operand)
    (success : (outcome s operand).result = .ok (quotient, remainder)) :
    SszNative.NatArithmetic.operandAt (widthLoad t) (r (.GPR 0#5) s).toNat quotient ∧
      widthLoad t ((r (.GPR 0#5) s).toNat + 16) 8 = some remainder.toNat ∧
      widthLoad t ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 ∧
      quotient.value = operand.value / (r (.GPR 3#5) s).toNat ∧
      remainder.toNat = operand.value % (r (.GPR 3#5) s).toNat ∧
      remainder.toNat < (r (.GPR 3#5) s).toNat := by
  have stored := post.result
  rw [success] at stored
  exact ⟨stored.1, stored.2.1, stored.2.2,
    SszNative.NatDivision.run_success operand (r (.GPR 3#5) s)
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used (quotient, remainder) success⟩

/-- Without allocation, only output and activation bytes may change. In
particular this protects arbitrary scratch observations outside those spans. -/
theorem Post.no_allocation_frame {s t : ArmState} {operand : SszNative.NatOperand}
    (post : Post s t operand) (unallocated : (outcome s operand).allocation = none) :
    MemoryFrame (localWrites s) s t := by
  simpa only [writesFor, unallocated] using post.frame

/-- The no-allocation path retains the exact original cursor, has no written
limbs, and preserves all 24 descriptor bytes, not just its immutable header. -/
theorem Post.no_allocation_resources {s t : ArmState} {operand : SszNative.NatOperand}
    (post : Post s t operand) (owned : Owned s operand)
    (unallocated : (outcome s operand).allocation = none) :
    read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t =
        read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s ∧
      (outcome s operand).written = [] ∧
      read_mem_bytes 24 (r (.GPR 4#5) s) t = read_mem_bytes 24 (r (.GPR 4#5) s) s := by
  have resources := SszNative.NatDivision.no_allocation_resources operand (r (.GPR 3#5) s)
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used unallocated
  refine ⟨?_, resources.2, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    exact post.cursor.trans resources.1
  · exact (post.no_allocation_frame unallocated).read _ 24 owned.arenaBound owned.arenaLocal

/-- Any scratch span disjoint from the local writes is byte-for-byte unchanged
when no allocation occurs; no disjointness between readonly spans is required. -/
theorem Post.no_allocation_scratch {s t : ArmState} {operand : SszNative.NatOperand}
    (post : Post s t operand) (unallocated : (outcome s operand).allocation = none)
    (address bytes : Nat) (scratch : Protected (localWrites s) address bytes) :
    ∀ a : BitVec 64, address ≤ a.toNat → a.toNat < address + bytes → t.mem a = s.mem a := by
  intro a low high
  exact (post.no_allocation_frame unallocated).protected_byte scratch a low high

end SszArm.NatDivision
