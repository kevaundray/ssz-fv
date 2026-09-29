import SszArm.HashImage
import SszArm.DelimitedMemory
import SszArm.WordNormalize
import SszHashStreamMemory
import SszHashStreamPublic

namespace SszArm.Hash

open Delimited (Span Protected MemoryFrame)

abbrev StreamState := SszNative.HashStream.State

def BytesAt (s : ArmState) (address : BitVec 64) (bytes : ByteArray) : Prop :=
  ∀ i : Fin bytes.size, s.mem (address + BitVec.ofNat 64 i.val) = bytes[i.val].toBitVec

def ChainingAt (s : ArmState) (address : BitVec 64) (words : Vector UInt32 8) : Prop :=
  ∀ i : Fin 8, read_mem_bytes 4 (address + BitVec.ofNat 64 (4 * i.val)) s =
    words[i.val].toBitVec

structure StateAt (s : ArmState) (address : BitVec 64) (value : StreamState) : Prop where
  buffer : BytesAt s address ⟨value.buffer.toArray⟩
  chaining : ChainingAt s (address + 64#64) value.chaining
  buffered : read_mem_bytes 8 (address + 96#64) s = BitVec.ofNat 64 value.buffered.val
  byteLen : read_mem_bytes 8 (address + 104#64) s = value.byteLen.toBitVec

structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

def TableAt (s : ArmState) (address : BitVec 64) (bytes : List UInt8) : Prop :=
  BytesAt s address ⟨bytes.toArray⟩

structure DataAt (s : ArmState) (base : BitVec 64) : Prop where
  initial : TableAt s (base + initialOffset) initialTable
  rounds : TableAt s (base + roundsOffset) roundsTable
  initialBound : (base + initialOffset).toNat + 32 ≤ 2^64
  roundsBound : (base + roundsOffset).toNat + 256 ≤ 2^64

def stackSpan (s : ArmState) (depth : Nat) : Span :=
  ((r (.GPR 31#5) s).toNat - depth, depth)

def compressionWrites (s : ArmState) : List Span :=
  [stackSpan s 160, ((r (.GPR 0#5) s).toNat, 32)]

structure CompressionOwned (s : ArmState) (base : BitVec 64)
    (words : Vector UInt32 8) (block : ByteArray) : Prop where
  blockSize : block.size = 64
  state : ChainingAt s (r (.GPR 0#5) s) words
  input : BytesAt s (r (.GPR 1#5) s) block
  stateBound : (r (.GPR 0#5) s).toNat + 32 ≤ 2^64
  inputBound : (r (.GPR 1#5) s).toNat + 64 ≤ 2^64
  stackLow : 160 ≤ (r (.GPR 31#5) s).toNat
  stateStack : Protected [stackSpan s 160] (r (.GPR 0#5) s).toNat 32
  inputOwned : Protected (compressionWrites s) (r (.GPR 1#5) s).toNat 64
  roundsOwned : Protected (compressionWrites s) (base + roundsOffset).toNat 256

/-- The sole trusted semantic boundary: real helper entry, real table, real run.
All premises describe the entry state; no wrapper/helper continuation is assumed. -/
def CompressionCorrect (base : BitVec 64) : Prop :=
  ∀ (s : ArmState) (words : Vector UInt32 8) (block : ByteArray),
    RowsAt s (base + compressOffset) compressProgram →
    TableAt s (base + roundsOffset) roundsTable →
    (base + roundsOffset).toNat + 256 ≤ 2^64 →
    read_pc s = base + compressOffset → read_err s = .None → CheckSPAlignment s →
    CompressionOwned s base words block →
    ∃ fuel, Returned s (run fuel s) ∧
      ChainingAt (run fuel s) (r (.GPR 0#5) s) (Ssz.Sha256.compress words block 0) ∧
      MemoryFrame (compressionWrites s) s (run fuel s)

def finalizeWrites (s : ArmState) : List Span :=
  [stackSpan s 192, ((r (.GPR 0#5) s).toNat, 32), ((r (.GPR 1#5) s).toNat, 112)]

structure FinalizeOwned (s : ArmState) (base : BitVec 64) (value : StreamState) : Prop where
  state : StateAt s (r (.GPR 1#5) s) value
  stateBound : (r (.GPR 1#5) s).toNat + 112 ≤ 2^64
  outputBound : (r (.GPR 0#5) s).toNat + 32 ≤ 2^64
  stackLow : 192 ≤ (r (.GPR 31#5) s).toNat
  stateStack : Protected [stackSpan s 192] (r (.GPR 1#5) s).toNat 112
  outputStack : Protected [stackSpan s 192] (r (.GPR 0#5) s).toNat 32
  outputState : Protected [((r (.GPR 1#5) s).toNat, 112)] (r (.GPR 0#5) s).toNat 32
  initialOwned : Protected (finalizeWrites s) (base + initialOffset).toNat 32
  roundsOwned : Protected (finalizeWrites s) (base + roundsOffset).toNat 256

structure FinalizePost (s t : ArmState) (value : StreamState) : Prop where
  returned : Returned s t
  bytes : BytesAt t (r (.GPR 0#5) s) (SszNative.HashStream.finalize value)
  frame : MemoryFrame (finalizeWrites s) s t

def combineWrites (s : ArmState) : List Span :=
  [stackSpan s 496, ((r (.GPR 0#5) s).toNat, 32)]

structure CombineOwned (s : ArmState) (base : BitVec 64) (left right : ByteArray) : Prop where
  leftLength : (r (.GPR 2#5) s).toNat = left.size
  rightLength : (r (.GPR 4#5) s).toNat = right.size
  leftBound : (r (.GPR 1#5) s).toNat + left.size ≤ 2^64
  rightBound : (r (.GPR 3#5) s).toNat + right.size ≤ 2^64
  outputBound : (r (.GPR 0#5) s).toNat + 32 ≤ 2^64
  stackLow : 496 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [stackSpan s 496] (r (.GPR 0#5) s).toNat 32
  leftOwned : Protected (combineWrites s) (r (.GPR 1#5) s).toNat left.size
  rightOwned : Protected (combineWrites s) (r (.GPR 3#5) s).toNat right.size
  initialOwned : Protected (combineWrites s) (base + initialOffset).toNat 32
  roundsOwned : Protected (combineWrites s) (base + roundsOffset).toNat 256
  left : BytesAt s (r (.GPR 1#5) s) left
  right : BytesAt s (r (.GPR 3#5) s) right

structure CombinePost (s t : ArmState) (left right : ByteArray) : Prop where
  returned : Returned s t
  bytes : BytesAt t (r (.GPR 0#5) s) (SszNative.HashStream.combine left right)
  frame : MemoryFrame (combineWrites s) s t
  left : BytesAt t (r (.GPR 1#5) s) left
  right : BytesAt t (r (.GPR 3#5) s) right

end SszArm.Hash
