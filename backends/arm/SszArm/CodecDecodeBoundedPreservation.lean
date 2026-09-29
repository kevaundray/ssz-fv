import SszArm.CodecDecodeBoundedContract

namespace SszArm.Codec.Decode.Bounded

open SszNative
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- Byte-frame transport at a raw record offset, with the original pointer
retained rather than normalized from an abstract payload. -/
theorem record_read {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (pointer : BitVec 64) (bytes offset width : Nat)
    (physical : pointer.toNat + bytes ≤ 2 ^ 64)
    (owned : Protected writes pointer.toNat bytes) (inside : offset + width ≤ bytes) :
    read_mem_bytes width (pointer + BitVec.ofNat 64 offset) t =
      read_mem_bytes width (pointer + BitVec.ofNat 64 offset) s := by
  have loaded := frame.load (pointer.toNat + offset) width (by omega)
    (owned.subspan offset width inside)
  apply BitVec.eq_of_toNat_eq
  exact Option.some.inj (by
    simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded)

theorem result_local_frame {s t : ArmState} (result : Except Codec.Error Unit)
    (frame : MemoryFrame (writesFor s result) s t) : MemoryFrame (localWrites s) s t := by
  intro address outside
  apply frame address
  intro span member
  simp only [writesFor, List.mem_cons] at member
  rcases member with rfl | stack
  · have output := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
    cases result <;> simp only [Prod.fst, Prod.snd] at * <;> omega
  · exact outside span (by simp only [localWrites, List.mem_cons]; exact Or.inr stack)

theorem inputs_preserved {s t : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (frame : MemoryFrame (localWrites s) s t) :
    LimitAt t (r (.GPR 1#5) s) limit ∧ ActualAt t (r (.GPR 2#5) s) actual := by
  constructor
  · cases limit with
    | none =>
      have tag := record_read frame (r (.GPR 1#5) s) 4 0 4 owned.limitBound
        owned.limitOwned (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at tag
      exact tag.trans owned.limitAt
    | some cap =>
      obtain ⟨tag, pointer, payload, limbs⟩ := owned.limitAt
      refine ⟨?_, ?_, ?_, NatDivision.operand_at_preserved frame cap limbs
        (owned.limitWords cap rfl)⟩
      · have load := record_read frame (r (.GPR 1#5) s) 24 0 4 owned.limitBound
          owned.limitOwned (by decide)
        simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at load
        exact load.trans tag
      · exact (record_read frame _ 24 8 8 owned.limitBound owned.limitOwned (by decide)).trans pointer
      · exact (record_read frame _ 24 16 8 owned.limitBound owned.limitOwned (by decide)).trans payload
  · obtain ⟨pointer, payload, limbs⟩ := owned.actualAt
    refine ⟨?_, ?_, NatDivision.operand_at_preserved frame actual limbs owned.actualWords⟩
    · have load := record_read frame (r (.GPR 2#5) s) 16 0 8 owned.actualBound
        owned.actualOwned (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at load
      exact load.trans pointer
    · exact (record_read frame _ 16 8 8 owned.actualBound owned.actualOwned (by decide)).trans payload

end SszArm.Codec.Decode.Bounded
