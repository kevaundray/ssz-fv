import SszArm.DelimitedMemory

namespace SszArm.Delimited

open BoolCodec
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- STP Q0,Q0 with MOVI-zeroed V0 writes thirty-two real zero bytes. -/
theorem write_zero32 (s : ArmState) (address : BitVec 64) :
    write_mem_bytes 32 address 0#256 s =
      write_mem_bytes 8 (address + 24#64) 0#64
        (write_mem_bytes 8 (address + 16#64) 0#64
          (write_mem_bytes 8 (address + 8#64) 0#64
            (write_mem_bytes 8 address 0#64 s))) := by
  simp [write_mem_bytes, BitVec.add_assoc]

/-- STR Q0 is a real sixteen-byte store, not an erased instruction. -/
theorem write_zero16 (s : ArmState) (address : BitVec 64) :
    write_mem_bytes 16 address 0#128 s =
      write_mem_bytes 8 (address + 8#64) 0#64 (write_mem_bytes 8 address 0#64 s) := by
  simp [write_mem_bytes, BitVec.add_assoc]

/-- Logical image common to the empty/no-delimiter/trailing-zero paths. This
lemma concerns the exact output memory; execution and activation are separate. -/
def zeroErrorMemory (s : ArmState) (out : BitVec 64) (reason : BitVec 32) : ArmState :=
  let s := write_mem_bytes 8 (out + 64#64) 0#64 s
  let s := write_mem_bytes 8 (out + 8#64) 1#64 s
  let s := write_mem_bytes 32 (out + 16#64) 0#256 s
  let s := write_mem_bytes 16 (out + 48#64) 0#128 s
  let s := write_mem_bytes 4 (out + 72#64) reason s
  write_mem_bytes 8 out 1#64 s

macro "delimited_side" : tactic => `(tactic|
  first
  | assumption
  | omega
  | (try simp -implicitDefEqProofs only [bitvec_to_nat] at *
     omega))

theorem zero_error_result (s : ArmState) (out : BitVec 64) (reason : BitVec 32)
    (physical : out.toNat + 76 ≤ 2^64) :
    SszNative.UintCodec.errorAt (widthLoad (zeroErrorMemory s out reason))
      out.toNat reason.toNat 0 0 := by
  simp (disch := delimited_side)
    [SszNative.UintCodec.errorAt, SszNative.NatMemory.At, SszNative.NatMemory.smallAt,
     widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, zeroErrorMemory,
     write_zero32, write_zero16, BitVec.add_assoc]

theorem zero_error_frame (s : ArmState) (out : BitVec 64) (reason : BitVec 32)
    (physical : out.toNat + 76 ≤ 2^64) :
    MemoryFrame [(out.toNat, 76)] s (zeroErrorMemory s out reason) := by
  intro a ha
  have outside := ha (out.toNat, 76) (by simp)
  simp only [Prod.fst, Prod.snd] at outside
  simp (disch := delimited_side) [zeroErrorMemory, ArmState.mem_w_eq_mem]

theorem empty_error_result (s : ArmState) (out : BitVec 64)
    (physical : out.toNat + 76 ≤ 2^64) :
    SszNative.BitView.ResultAt (widthLoad (zeroErrorMemory s out 16#32))
      out.toNat (.error .emptyEncoding) :=
  zero_error_result s out 16#32 physical

theorem no_delimiter_result (s : ArmState) (out : BitVec 64)
    (physical : out.toNat + 76 ≤ 2^64) :
    SszNative.BitView.ResultAt (widthLoad (zeroErrorMemory s out 17#32))
      out.toNat (.error .noDelimiter) :=
  zero_error_result s out 17#32 physical

theorem trailing_zeros_result (s : ArmState) (out : BitVec 64)
    (physical : out.toNat + 76 ≤ 2^64) :
    SszNative.BitView.ResultAt (widthLoad (zeroErrorMemory s out 18#32))
      out.toNat (.error .trailingZeros) :=
  zero_error_result s out 18#32 physical

end SszArm.Delimited
