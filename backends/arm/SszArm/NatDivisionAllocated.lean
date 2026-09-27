import SszArm.NatDivisionPhysical
import SszArm.NatDivisionReturn
import SszNatOperandNormalization

namespace SszArm.NatDivision

open Delimited (Protected)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem fromWords_owned (writes : List Delimited.Span) (pointer : BitVec 64)
    (words : List (BitVec 64)) (payloadOwned : Protected writes pointer.toNat (8 * words.length)) :
    OperandOwned writes (SszNative.NatOperand.fromWords pointer words) := by
  have length : (SszNative.Limbs.trim words).length ≤ words.length := by
    rw [SszNative.Limbs.trim_length]
    exact SszNative.Limbs.sigWords_le_length words
  cases trimmed : SszNative.Limbs.trim words with
  | nil => simp only [SszNative.NatOperand.fromWords, trimmed, OperandOwned]
  | cons first rest =>
    cases rest with
    | nil => simp only [SszNative.NatOperand.fromWords, trimmed, OperandOwned]
    | cons second rest =>
      have keep := payloadOwned.subspan 0 (8 * (SszNative.Limbs.trim words).length) (by omega)
      simpa only [SszNative.NatOperand.fromWords, trimmed, OperandOwned, Nat.add_zero] using keep

theorem allocated_operand_at {original s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (written : WrittenAt (widthLoad s) (outcome original operand)) :
    (SszNative.NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
      (outcome original operand).written).At (widthLoad s) := by
  have geometry := owned.allocation_geometry reservation allocated
  apply SszNative.NatOperand.fromWords_at
  have bounded := geometry.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using geometry.1
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using geometry.2.2.1
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using geometry.2.2.2
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using written reservation allocated

theorem allocated_output_protected {original s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original) :
    Protected (returnWrites s) reservation.pointer (8 * (outcome original operand).written.length) := by
  have lower := owned.stackBound
  rcases owned.fresh reservation allocated with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    simp only [returnWrites, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · rw [out]
      exact separate ((r (.GPR 0#5) original).toNat, 68) (by simp [localWrites])
    · have apart := separate ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at apart ⊢
      rw [sp]
      bv_omega

theorem allocated_operand_owned {original s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original) :
    OperandOwned (returnWrites s) (SszNative.NatOperand.fromWords
      (BitVec.ofNat 64 reservation.pointer) (outcome original operand).written) := by
  apply fromWords_owned
  have bounded := (owned.allocation_geometry reservation allocated).2.1
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using
    allocated_output_protected owned reservation allocated sp out

theorem fromWords_two (pointer low high : BitVec 64) (nonzero : high ≠ 0#64) :
    SszNative.NatOperand.fromWords pointer [low, high] = .large pointer [low, high] := by
  simp [SszNative.NatOperand.fromWords, SszNative.Limbs.trim, nonzero]

end SszArm.NatDivision
