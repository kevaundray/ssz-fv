import SszArm.BitVectorResources
import SszArm.BitVectorQuotient
import SszArm.NatAddLargeCorrectMemory

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (Protected MemoryFrame)

/-- Every fixed-size leaf result and its nested lowering spill fit inside the
body's already owned temporary interval. -/
theorem leaf_locals_covered {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (bytes : Nat) (size : bytes ≤ 128)
    (output : r (.GPR 0#5) c = r (.GPR 31#5) s + 144#64)
    (sp : r (.GPR 31#5) c = r (.GPR 31#5) s) :
    Covers (localWrites s)
      [((r (.GPR 0#5) c).toNat, bytes), ((r (.GPR 31#5) c).toNat - 16, 16)] := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have outNat : (r (.GPR 0#5) c).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    rw [output]
    bv_omega
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨((r (.GPR 31#5) s).toNat - 80, 352), by simp [localWrites],
      by simp only [outNat]; omega, by simp only [outNat]; omega⟩
  · exact ⟨((r (.GPR 31#5) s).toNat - 80, 352), by simp [localWrites],
      by simp only [sp]; omega, by simp only [sp]; omega⟩

theorem narrow_owned {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (frame : MemoryFrame (writesFor s (outcome s length data)) s c)
    (output : r (.GPR 0#5) c = r (.GPR 31#5) s + 144#64)
    (sp : r (.GPR 31#5) c = r (.GPR 31#5) s)
    (pointer : r (.GPR 1#5) c = length.pointer)
    (payload : r (.GPR 2#5) c = length.payload) : NatToU128.Owned c length := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have outNat : (r (.GPR 0#5) c).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    rw [output]
    bv_omega
  refine ⟨pointer, payload, ?_, ?_, ?_, ?_, ?_⟩
  · exact NatDivision.operand_at_preserved frame length owned.descriptor.2.2 owned.operandOwned
  · rw [outNat]; omega
  · rw [sp]; omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [outNat, sp]
    right
    omega
  · exact ((local_covered s (outcome s length data)).trans
      (leaf_locals_covered owned 32 (by decide) output sp)).operand length owned.operandOwned

/-- Exact receives the stack copy at SP+48, not the original descriptor; the
limb buffer itself is protected by its quotient/rounding provenance. -/
theorem exact_owned {s c : ArmState} {length expected : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (output : r (.GPR 0#5) c = r (.GPR 31#5) s + 144#64)
    (sp : r (.GPR 31#5) c = r (.GPR 31#5) s)
    (pairPointer : r (.GPR 1#5) c = r (.GPR 31#5) s + 48#64)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c) (r (.GPR 1#5) c).toNat expected)
    (limbs : NatDivision.OperandOwned (localWrites s) expected) : NatExact.Owned c expected := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have outNat : (r (.GPR 0#5) c).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    rw [output]
    bv_omega
  have pairNat : (r (.GPR 1#5) c).toNat = (r (.GPR 31#5) s).toNat + 48 := by
    rw [pairPointer]
    bv_omega
  refine ⟨pair, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairNat]; omega
  · right
    intro span member
    simp only [NatExact.localWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · left; simp only [pairNat, outNat]; omega
    · right; simp only [pairNat, sp]; omega
  · exact (leaf_locals_covered owned 68 (by decide) output sp).operand expected limbs
  · rw [outNat]; omega
  · rw [sp]; omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    simp only [outNat, sp]
    omega

theorem quotient_local_owned {s : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (success : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder)) :
    NatDivision.OperandOwned (localWrites s) quotient := by
  rcases quotient_origin length quotient remainder (arenaOf s).base (arenaOf s).capacity
    (arenaOf s).used success with ⟨value, rfl⟩ | ⟨reservation, allocated, rfl⟩
  · trivial
  · have fresh := owned.fresh _ (divided_write s length data reservation allocated)
    have cover : Covers (localWrites s ++
        [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)])
        (localWrites s) := by
      intro span member
      exact ⟨span, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩
    have separated := cover.protected fresh
    have size := (SszNative.NatDivision.allocation_resources length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used reservation allocated).2.1
    have positive : 0 < (SszNative.NatDivision.run length 8 (arenaOf s).base
        (arenaOf s).capacity (arenaOf s).used).written.length := by
      split at size <;> omega
    have endAddress := division_allocation_end length (arenaOf s) reservation allocated
    have cursor := (division_cursor_bounds s length data owned).2
    rw [outcome, divided_eq] at cursor
    have storage := owned.arenaStorage
    have pointerBound : reservation.pointer < 2^64 := by omega
    change NatAdd.OperandOwned (localWrites s) _
    apply NatAdd.LargeCorrect.fromWords_owned
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using separated

end SszArm.BitVector
