import SszArm.DelimitedZeroMemory
import SszArm.UintResultMemory

namespace SszArm.Delimited

open BoolCodec
open UintCodec (widthLoad)
open UintCodec.Tail (write_pair_words)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem MemoryFrame.bytes {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (pointer : BitVec 64) (data : Ssz.Bytes)
    (physical : pointer.toNat + data.size ≤ 2^64)
    (owned : Protected writes pointer.toNat data.size)
    (input : SszNative.ByteView.BytesAt (widthLoad s) pointer.toNat data) :
    SszNative.ByteView.BytesAt (widthLoad t) pointer.toNat data := by
  intro i hi
  have byteOwned : Protected writes (pointer.toNat + i) 1 := by
    right
    intro span member
    rcases owned with empty | separate
    · omega
    · have hsep := separate span member
      omega
  rw [frame.load _ _ (by omega) byteOwned]
  exact input i hi

def successMemory (s : ArmState) (out pointer : BitVec 64) (bytes count : Nat) : ArmState :=
  let s := write_mem_bytes 16 (out + 32#64) (BitVec.ofNat 64 bytes ++ pointer) s
  let s := write_mem_bytes 1 (out + 16#64) 3#8 s
  let s := write_mem_bytes 16 (out + 48#64)
    (BitVec.ofNat 64 (count / 2^64) ++ BitVec.ofNat 64 count) s
  write_mem_bytes 8 out 0#64 s

theorem success_memory_frame (s : ArmState) (out pointer : BitVec 64) (bytes count : Nat)
    (physical : out.toNat + 76 ≤ 2^64) :
    MemoryFrame [(out.toNat, 76)] s (successMemory s out pointer bytes count) := by
  intro a ha
  have outside := ha (out.toNat, 76) (by simp)
  simp only [Prod.fst, Prod.snd] at outside
  simp (disch := delimited_side) [successMemory, ArmState.mem_w_eq_mem]

/-- Success borrows exactly the original pointer and retained byte count; no
output payload copy or hidden allocation is introduced by this observation. -/
theorem success_memory_result (s : ArmState) (out pointer : BitVec 64)
    (packed : Ssz.Bytes) (count : Nat)
    (output : out.toNat + 76 ≤ 2^64) (physical : pointer.toNat + packed.size ≤ 2^64)
    (bytesBound : packed.size < 2^64) (countBound : count < 2^128)
    (scope : packed.size = (count + 7) / 8)
    (owned : Protected [(out.toNat, 76)] pointer.toNat packed.size)
    (input : SszNative.ByteView.BytesAt (widthLoad s) pointer.toNat packed) :
    SszNative.BitView.ResultAt (widthLoad (successMemory s out pointer packed.size count))
      out.toNat (.ok (.bits (Ssz.unpackBits packed count))) := by
  have frame := success_memory_frame s out pointer packed.size count output
  have retained := frame.bytes pointer packed physical owned input
  have size : (Ssz.unpackBits packed count).size = count := by simp [Ssz.unpackBits]
  have highBound : count / 2^64 < 2^64 := by omega
  simp only [SszNative.BitView.ResultAt, size]
  refine ⟨?_, ?_, countBound, ?_, ?_, pointer.toNat, packed, ?_, ?_, scope, retained, rfl⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    simp (disch := delimited_side)
      [successMemory, write_pair_words, BitVec.add_assoc,
       BitVec.toNat_ofNat, Nat.mod_eq_of_lt bytesBound, Nat.mod_eq_of_lt highBound]

def overLimitMemory (s : ArmState) (out expectedPtr expectedWord actualPtr actualWord : BitVec 64) : ArmState :=
  let s := write_mem_bytes 8 (out + 56#64) 0#64 s
  let s := write_mem_bytes 8 (out + 64#64) 0#64 s
  let s := write_mem_bytes 8 (out + 8#64) 1#64 s
  let s := write_mem_bytes 8 (out + 16#64) 0#64 s
  let s := write_mem_bytes 16 (out + 24#64) (expectedWord ++ expectedPtr) s
  let s := write_mem_bytes 8 (out + 40#64) actualPtr s
  let s := write_mem_bytes 8 (out + 48#64) actualWord s
  let s := write_mem_bytes 4 (out + 72#64) 2#32 s
  write_mem_bytes 8 out 1#64 s

theorem over_limit_memory_frame (s : ArmState)
    (out expectedPtr expectedWord actualPtr actualWord : BitVec 64)
    (physical : out.toNat + 76 ≤ 2^64) :
    MemoryFrame [(out.toNat, 76)] s
      (overLimitMemory s out expectedPtr expectedWord actualPtr actualWord) := by
  intro a ha
  have outside := ha (out.toNat, 76) (by simp)
  simp only [Prod.fst, Prod.snd] at outside
  simp (disch := delimited_side) [overLimitMemory, ArmState.mem_w_eq_mem]

/-- The error retains both original Nat representations, including arbitrarily
large noncanonical caps, immutable aliases, and empty borrowed limb arrays. -/
theorem over_limit_memory_result (s : ArmState)
    (out expectedPtr expectedWord actualPtr actualWord : BitVec 64) (expected actual : Nat)
    (physical : out.toNat + 76 ≤ 2^64)
    (expectedPair : SszNative.NatMemory.Pair (widthLoad s) expectedPtr expectedWord expected)
    (actualPair : SszNative.NatMemory.Pair (widthLoad s) actualPtr actualWord actual)
    (expectedOwned : NatOwned [(out.toNat, 76)] expectedPtr expectedWord)
    (actualOwned : NatOwned [(out.toNat, 76)] actualPtr actualWord) :
    SszNative.BitView.ResultAt
      (widthLoad (overLimitMemory s out expectedPtr expectedWord actualPtr actualWord))
      out.toNat (.error (.overLimit expected actual)) := by
  have frame := over_limit_memory_frame s out expectedPtr expectedWord actualPtr actualWord physical
  have ep := frame.pair expectedPtr expectedWord expected expectedPair expectedOwned
  have ap := frame.pair actualPtr actualWord actual actualPair actualOwned
  change SszNative.UintCodec.errorAt _ _ 2 expected actual
  refine ⟨?_, ?_, ?_,
    SszNative.NatMemory.Pair.at _ _ _ _ _ ep ?_ ?_,
    SszNative.NatMemory.Pair.at _ _ _ _ _ ap ?_ ?_,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    simp (disch := delimited_side) [overLimitMemory, write_pair_words, BitVec.add_assoc]

end SszArm.Delimited
