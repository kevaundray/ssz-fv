import SszArm.DispatchBitVectorContract

namespace SszArm.Dispatch.BitVector

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)
open SszArm.BitVector (Covers)

theorem bodySP_nat {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : (bodySP s).toNat = (r (.GPR 31#5) s).toNat - 368 := by
  have low := owned.stackLow
  simp only [bodySP]
  bv_omega

theorem saved_covered (s : ArmState) (result : SszNative.BitVector.Outcome) :
    Covers (writesFor s result) [savedSpan s] := by
  intro span member
  exact ⟨span, List.mem_append_right _ member, Nat.le_refl _, Nat.le_refl _⟩

theorem body_covered (s : ArmState) (result : SszNative.BitVector.Outcome) :
    Covers (writesFor s result) (bodyWrites s result) := by
  intro span member
  exact ⟨span, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩

theorem entry_frame {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : MemoryFrame [savedSpan s] s (entered s .bitVector) := by
  intro address outside
  have apart := outside (savedSpan s) (by simp)
  have low := owned.stackLow
  apply entered_frame s .bitVector (by omega)
  simp only [savedSpan] at apart
  omega

theorem dispatch_owned {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : EntryOwned s .bitVector := by
  have low := owned.stackLow
  have bound := owned.descriptorBound
  refine ⟨by omega, by omega, ?_, owned.tag⟩
  have protect := (saved_covered s (outcome s length data)).protected owned.descriptorOwned
  rcases protect with empty | separate
  · omega
  · have apart := separate (savedSpan s) (by simp)
    simp only [savedSpan] at apart
    omega

theorem arena_read {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (offset : Nat) (within : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) (entered s .bitVector) =
      read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) s := by
  have low := owned.stackLow
  have bound := owned.arenaBound
  rcases owned.arenaLocal with empty | separate
  · omega
  · have apart := separate (savedSpan s) (by simp)
    simp only [savedSpan] at apart
    apply entered_read s .bitVector (by omega) _ 8 <;> bv_omega

theorem entered_arenaOf {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : SszArm.BitVector.arenaOf (entered s .bitVector) = arenaOf s := by
  have base := arena_read owned 0 (by decide)
  have capacity := arena_read owned 8 (by decide)
  have used := arena_read owned 16 (by decide)
  simp only [BitVec.add_zero] at base
  simp only [SszArm.BitVector.arenaOf, arenaOf, NatDivision.arenaOf, entered_arena,
    base, capacity, used]

theorem entered_outcome {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    SszArm.BitVector.outcome (entered s .bitVector) length data = outcome s length data := by
  rw [SszArm.BitVector.outcome, entered_arenaOf owned]
  rfl

theorem entered_available {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    SszArm.BitVector.availableSpan (entered s .bitVector) = availableSpan s := by
  simp only [SszArm.BitVector.availableSpan, availableSpan, entered_arenaOf owned]

theorem entered_locals {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : SszArm.BitVector.localWrites (entered s .bitVector) = localWrites s := by
  simp (config := {decide := true}) only [SszArm.BitVector.localWrites, localWrites,
    entered_reg, entered_sp, bodySP_nat owned, Nat.sub_sub]

theorem entered_bodyWrites {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    SszArm.BitVector.writesFor (entered s .bitVector)
      (SszArm.BitVector.outcome (entered s .bitVector) length data) = bodyWrites s (outcome s length data) := by
  simp only [SszArm.BitVector.writesFor, bodyWrites, entered_locals owned,
    entered_outcome owned, entered_arena]

theorem entered_input {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    SszNative.ByteView.BytesAt (widthLoad (entered s .bitVector)) (r (.GPR 2#5) s).toNat data := by
  intro index within
  have bound := owned.inputBound
  have protect := (saved_covered s (outcome s length data)).protected owned.inputOwned
  rw [(entry_frame owned).load _ 1 (by omega) (protect.subspan index 1 (by omega))]
  exact owned.input index within

theorem entered_descriptor {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    SszNative.NatArithmetic.operandAt (widthLoad (entered s .bitVector))
      ((r (.GPR 1#5) s).toNat + 8) length := by
  have bound := owned.descriptorBound
  have protect := (saved_covered s (outcome s length data)).protected owned.descriptorOwned
  refine ⟨?_, ?_, ?_⟩
  · rw [(entry_frame owned).load _ 8 (by omega) (protect.subspan 8 8 (by omega))]
    exact owned.descriptor.1
  · rw [(entry_frame owned).load _ 8 (by omega)
      (by simpa only [Nat.add_assoc] using protect.subspan 16 8 (by omega))]
    exact owned.descriptor.2.1
  · exact NatDivision.operand_at_preserved (entry_frame owned) length owned.descriptor.2.2
      ((saved_covered s (outcome s length data)).operand length owned.operandOwned)

end SszArm.Dispatch.BitVector
