import SszArm.BitVectorPaddingGateExec

namespace SszArm.BitVector.PaddingGate

open TailCheck
open UintCodec (widthLoad)

def Bad (remainder : BitVec 64) (data : Ssz.Bytes) : Prop :=
  remainder ≠ 0#64 ∧ 0 < data.size ∧
    data[data.size - 1]! >>> UInt8.ofNat remainder.toNat ≠ 0

instance (remainder : BitVec 64) (data : Ssz.Bytes) : Decidable (Bad remainder data) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem masked_count (remainder : BitVec 64) (bound : remainder.toNat < 8) :
    ((remainder.setWidth 32 &&& 7#32).setWidth 64) = remainder := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  change (remainder.setWidth 32).toNat &&& (2^3 - 1) = remainder.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth]
  omega

theorem native_shift_zero (byte : UInt8) (remainder : BitVec 64)
    (bound : remainder.toNat < 8) :
    (byte.toBitVec.setWidth 32 >>> remainder.toNat) = 0#32 ↔
      byte >>> UInt8.ofNat remainder.toNat = 0 := by
  rw [← BitVec.toNat_inj, ← UInt8.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32),
    BitVec.toNat_ofNat, UInt8.toNat_shiftRight, UInt8.toNat_ofNat', UInt8.toNat_ofNat,
    Nat.mod_eq_of_lt (show remainder.toNat < 2^8 by omega), Nat.mod_eq_of_lt bound]
  rfl

theorem prepared_last {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) (base : BitVec 64) (nonempty : 0 < data.size)
    (bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data) :
    read_mem_bytes 1 (r (.GPR 24#5) c + r (.GPR 20#5) c - 1#64)
      (prepared c base) = data[data.size - 1]!.toBitVec := by
  have saved := bytes_after_frame owned (prepared_frame owned current.sp base) bytes
  have last := Delimited.last_byte (prepared c base) (r (.GPR 2#5) s)
    (r (.GPR 3#5) s) data owned.length nonempty saved
  have address : r (.GPR 24#5) c + r (.GPR 20#5) c - 1#64 =
      r (.GPR 2#5) s + (r (.GPR 3#5) s - 1#64) := by
    rw [current.input, current.size]
    bv_omega
  simpa only [address] using last

theorem restored_count {s c : ArmState} {length expected : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) (base : BitVec 64)
    (arithmetic : SszNative.BitVector.Expected length expected remainder) :
    r (.GPR 9#5) (restored c base) = remainder := by
  have bound := SszNative.BitVector.expected_remainder_bound arithmetic
  have count := masked_count remainder bound
  have low := owned.stackLow
  have physical : (r (.GPR 31#5) c - 16#64).toNat + 8 ≤ 2^64 := by
    rw [current.sp]
    bv_omega
  simp (config := {decide := true, instances := true}) only
    [restored, loaded, prepared, Stage.result, state_simp_rules, current.remainderValue, count]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same c 8
    (r (.GPR 31#5) c - 16#64) remainder physical

theorem restored_byte {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) (base : BitVec 64) (nonempty : 0 < data.size)
    (bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data) :
    r (.GPR 8#5) (restored c base) = data[data.size - 1]!.toBitVec.setWidth 64 := by
  have last := prepared_last owned current base nonempty bytes
  simp (config := {decide := true, instances := true}) only
    [restored, loaded, Stage.result, state_simp_rules]
  simpa (config := {decide := true, instances := true}) only
    [prepared, Stage.result, state_simp_rules] using congrArg (BitVec.setWidth 64) last

theorem checked_pc {s c : ArmState} {length expected : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) (base : BitVec 64) (nonempty : 0 < data.size)
    (bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data)
    (arithmetic : SszNative.BitVector.Expected length expected remainder) :
    read_pc (checked c base) =
      if data[data.size - 1]! >>> UInt8.ofNat remainder.toNat = 0
      then base + 6576#64 else base + 6052#64 := by
  have bound := SszNative.BitVector.expected_remainder_bound arithmetic
  have count : (remainder.setWidth 32).toNat % 32 = remainder.toNat := by
    simp only [BitVec.toNat_setWidth]
    omega
  simp (config := {decide := true, instances := true}) only
    [checked, Stage.result, state_simp_rules, restored_count owned current base arithmetic,
     restored_byte owned current base nonempty bytes, count,
     BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
     native_shift_zero _ remainder bound]

theorem padding_space {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) : Padding.Space c := by
  have low := owned.stackLow
  refine ⟨?_, ?_, ?_⟩
  · rw [current.sp]; omega
  · rw [current.output]; exact owned.outputBound
  · rw [current.output, current.sp]
    rcases owned.outputStack with empty | separated
    · omega
    · have disjoint := separated ((r (.GPR 31#5) s).toNat - 80, 448) (by simp)
      omega

theorem padding_cover {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) : Covers (localWrites s) (Padding.writes c) := by
  have low := owned.stackLow
  intro span member
  simp only [Padding.writes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨((r (.GPR 0#5) s).toNat, 80), by simp [localWrites], ?_, ?_⟩ <;>
      simp only [current.output, Nat.le_refl]
  · refine ⟨((r (.GPR 31#5) s).toNat - 80, 352), by simp [localWrites], ?_, ?_⟩ <;>
      simp only [current.sp] <;> omega

end SszArm.BitVector.PaddingGate
