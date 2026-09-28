import SszArm.EmitScalarProgram
import SszArm.EmitUintProgram
import SszArm.EmitBitsProgram
import SszArm.EmitOutput

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)

/-- Every successful primitive logical call executes the actual private entry,
all required linked helper calls, and its original-LR RET. There is no readable
Plan, initialized result/output-prefix, precomputed path, or future-state premise.

The input observations cover the original active descriptor/value spans and all
original borrowed Nat limbs and backing bytes. Inactive object padding is only
preserved where it lies outside the explicitly permitted physical write frame. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value) (size : Nat)
    (owned : Owned s (Args.ofEntry s) desc value size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : ∃ fuel, Post s (run fuel s) desc value size := by
  have compatible := compatible_of_expected owned.expected
  cases desc with
  | bool =>
    cases value with
    | bool flag => exact bool_program_correct s base flag size owned code error aligned pc
    | _ => cases compatible
  | uint width =>
    cases value with
    | uint number => exact uint_program_correct s base width number size owned code error aligned pc
    | _ => cases compatible
  | byteVector length =>
    cases value with
    | bytes bytes =>
      exact bytes_program_correct s base (.byteVector length) bytes size
        ⟨length, Or.inl rfl⟩ owned code error aligned pc
    | _ => cases compatible
  | byteList limit =>
    cases value with
    | bytes bytes =>
      exact bytes_program_correct s base (.byteList limit) bytes size
        ⟨limit, Or.inr rfl⟩ owned code error aligned pc
    | _ => cases compatible
  | bitVector length =>
    cases value with
    | bits bits =>
      exact bits_program_correct s base (.bitVector length) bits size
        (by trivial) owned code error aligned pc
    | _ => cases compatible
  | bitList limit =>
    cases value with
    | bits bits =>
      exact bits_program_correct s base (.bitList limit) bits size
        (by trivial) owned code error aligned pc
    | _ => cases compatible
  | progressiveBitList limit =>
    cases value with
    | bits bits =>
      exact bits_program_correct s base (.progressiveBitList limit) bits size
        (by trivial) owned code error aligned pc
    | _ => cases compatible

/-- The original-entry machine result refines the pinned serializer's exact
bytes and length, together with success status, ABI restoration, spare-output
preservation and the complete active-input/write-frame postcondition. -/
theorem program_refines (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value) (size : Nat)
    (owned : Owned s (Args.ofEntry s) desc value size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
      Post s (run fuel s) desc value size ∧
      SszNative.ByteView.BytesAt (UintCodec.widthLoad (run fuel s)) (Args.ofEntry s).output.toNat bytes ∧
      read_mem_bytes 8 (Args.ofEntry s).result (run fuel s) = BitVec.ofNat 64 bytes.size ∧
      read_mem_bytes 4 ((Args.ofEntry s).result + 64#64) (run fuel s) = 0#32 := by
  obtain ⟨fuel, post⟩ := program_correct s base desc value size owned code error aligned pc
  obtain ⟨bytes, encoding, length, output, written, status⟩ := post.encoding owned.expected
  exact ⟨fuel, bytes, encoding, length, post, output, written, status⟩

end SszArm.Emit
