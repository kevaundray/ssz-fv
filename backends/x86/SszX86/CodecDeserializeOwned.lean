import SszX86.CodecDeserializeEffects
import SszX86.CodecDeserializeImpl
import SszX86.CodecDecodeFixedImpl
import SszX86.CodecDecodeOffsetsImpl
import SszX86.CodecDecodeListImpl
import SszX86.CodecDecodeStructValuesImpl
import SszX86.CodecIsFixedImpl
import SszX86.CodecMeasureFixedImpl
import SszX86.CodecReadOffsetImpl
import SszX86.CodecBoundedImpl
import SszX86.CodecNatCmpUsizeImpl
import SszX86.CodecStack
import SszX86.CodecError
import SszX86.DispatchOwned
import SszX86.MeasureOwned
import SszX86.BitVectorCore
import SszX86.BitListImpl
import SszX86.NatMulImpl
import SszX86.NatMulWordImpl
import SszX86.NatMulMemsetEmbedded
import SszX86.BitVectorMapping

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative UintCodec

/-- The existing primitive entry provider reaches 472 bytes below entry SP,
including the decoder's 360-byte activation. Its remaining 112 bytes dominate
Nat::mul's 96, division's 64 and addition's 48. Recursive codec activations and
ordinary CALL slots are included separately in each descriptor layer. -/
def stackBytes (desc : SszNative.Codec.Desc) : Nat := Codec.descriptorStackBytes desc 112

def decodeFixedOffset : Int := decodeListOffset + CodecDecodeList.decodeFixedOffset
def decodeOffsetsOffset : Int := decodeListOffset + CodecDecodeList.decodeOffsetsOffset
def boundedOffset : Int := decodeListOffset + CodecDecodeList.boundedOffset

/-- Only fetched instructions and linked targets occur here. In particular no
recursive decoder result, successful helper call, or branch is assumed. -/
structure HelpersAt (e : Executable) (base : Int64) : Prop where
  bitVector : SszX86.BitVector.JointCodeAt e base
  bitList : BitList.JointCodeAt e base
  mul : NatMul.CodeAt e (base + Int64.ofInt natMulOffset)
  mulWord : NatMulWord.CodeAt e (base + Int64.ofInt natMulWordOffset)
  memset : NatMul.MemsetCall.MemsetCodeAt e
    (base + Int64.ofInt natMulOffset + Int64.ofNat NatMul.memsetOffset)
  fixed : CodecDecodeFixed.CodeAt e (base + Int64.ofInt decodeFixedOffset)
  offsets : CodecDecodeOffsets.CodeAt e (base + Int64.ofInt decodeOffsetsOffset)
  list : CodecDecodeList.CodeAt e (base + Int64.ofInt decodeListOffset)
  structValues : CodecDecodeStructValues.CodeAt e (base + Int64.ofInt decodeStructValuesOffset)
  classifier : CodecIsFixed.CodeAt e (base + Int64.ofInt isFixedOffset)
  fixedSize : CodecMeasureFixed.CodeAt e (base + Int64.ofInt measureFixedOffset)
  offset : CodecReadOffset.CodeAt e (base + Int64.ofInt readOffsetOffset)
  bounded : CodecBounded.CodeAt e (base + Int64.ofInt boundedOffset)
  compare : CodecNatCmpUsize.CodeAt e (base + Int64.ofInt natCmpUsizeOffset)

/-- Potential write ownership is not a claim that reserved storage is initialized.
An empty free interval has no points and imposes no separation restriction. -/
def Available (s : MachineData) (desc : SszNative.Codec.Desc)
    (address capacity used : BitVec 64) : Codec.Footprint := fun a =>
  Codec.InSpan a s.regs.rdi.toBitVec 80 ∨
  Codec.InSpan a (s.regs.r8.toBitVec + 16) 8 ∨
  Codec.InSpan a (address + used) (capacity.toNat - used.toNat) ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Raw physical ownership at the original native ABI. All readonly declarations,
Nat limbs, input bytes and already-used arena storage may alias one another.
Logical Nat values are not bounded by physical register widths. -/
structure Owned (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (input : CodecDecode.Input) (source : BitVec 64) (readonly : Codec.Footprint)
    (address capacity used ra : BitVec 64) : Prop where
  descriptor : Codec.DescAt s.dmem readonly s.regs.rsi.toBitVec desc
  descriptorMapped : Large.Mapped s.dmem s.regs.rsi.toBitVec 40
  inputPointer : s.regs.rdx.toBitVec = source + BitVec.ofNat 64 input.offset
  inputLength : input.bytes.size = s.regs.rcx.toNat
  inputPhysical : input.bytes.size < 2 ^ 63
  inputBound : source.toNat + input.offset + input.bytes.size ≤ 2 ^ 64
  inputStored : Large.BytesAt s.dmem s.regs.rdx.toBitVec input.bytes
  inputReadonly : ∀ a, Codec.InSpan a s.regs.rdx.toBitVec input.bytes.size → readonly a
  arena : Measure.ArenaAt s.dmem s.regs.r8.toBitVec address capacity used
  usedBound : used.toNat ≤ capacity.toNat
  arenaBound : address.toNat + capacity.toNat ≤ 2 ^ 64
  arenaNonzero : 0 < capacity.toNat → 0 < address.toNat
  arenaMapped : Large.Mapped s.dmem address capacity.toNat
  resultBound : s.regs.rdi.toNat + 80 ≤ 2 ^ 64
  resultAligned : s.regs.rdi.toNat % 16 = 0
  resultNonzero : 0 < s.regs.rdi.toNat
  resultMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 80
  headerBound : s.regs.r8.toNat + 24 ≤ 2 ^ 64
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec (stackBytes desc)
  stackAligned : s.regs.rsp.toNat % 8 = 0
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  resultHeader : Large.Disjoint s.regs.rdi.toBitVec s.regs.r8.toBitVec 80 24
  resultStack : Large.Disjoint s.regs.rdi.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) 80 (stackBytes desc + 8)
  headerStack : Large.Disjoint s.regs.r8.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) 24 (stackBytes desc + 8)
  freeResult : Large.Disjoint (address + used) s.regs.rdi.toBitVec
    (capacity.toNat - used.toNat) 80
  freeHeader : Large.Disjoint (address + used) s.regs.r8.toBitVec
    (capacity.toNat - used.toNat) 24
  freeStack : Large.Disjoint (address + used)
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc))
    (capacity.toNat - used.toNat) (stackBytes desc + 8)
  readonlyDisjoint : ∀ a, readonly a → ¬ Available s desc address capacity used a
  table : TableAt s.dmem base
  tableReadonly : ∀ a, Codec.InSpan a (tableAddress base) 52 → readonly a
  classifierTable : CodecIsFixed.TableAt s.dmem (base + Int64.ofInt isFixedOffset)
  classifierTableReadonly : ∀ a,
    Codec.InSpan a (CodecIsFixed.tableAddress (base + Int64.ofInt isFixedOffset)) 48 → readonly a
  fixedSizeTable : CodecMeasureFixed.TableAt s.dmem (base + Int64.ofInt measureFixedOffset)
  fixedSizeTableReadonly : ∀ a,
    Codec.InSpan a (CodecMeasureFixed.tableAddress (base + Int64.ofInt measureFixedOffset)) 48 → readonly a

def ResultFootprint (readonly : Codec.Footprint) (out : BitVec 64)
    (effects : List CodecDecode.Effect) : Codec.Footprint := fun a =>
  readonly a ∨ Codec.InSpan a out 80 ∨ EffectWrites effects a

/-- Only active Value fields are initialized by this observation. Native copies
may copy physical padding, but no padding byte is assigned a semantic value. -/
def ResultAt (m : DataMem) (readable : Codec.Footprint) (source out : BitVec 64) :
    Except SszNative.Codec.Error CodecDecode.Node → Prop
  | .ok node => widthLoad m out.toNat 8 = some 0 ∧
      Codec.NodeAt m readable source (out + 16) node
  | .error reason => Codec.DecodeErrorAt (widthLoad m) out.toNat reason

/-- Unwritten typed reservation suffixes and alignment gaps are excluded. -/
def Writable (s : MachineData) (desc : SszNative.Codec.Desc)
    (effects : List CodecDecode.Effect) : Codec.Footprint := fun a =>
  Codec.InSpan a s.regs.rdi.toBitVec 80 ∨ EffectWrites effects a ∨
  Codec.InSpan a (s.regs.r8.toBitVec + 16) 8 ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Canonical all-shape native postcondition: exact shared addressed nodes,
failures, initialized prefix storage, committed cursor, ABI and outside frame. -/
structure Post (s : MachineData) (desc : SszNative.Codec.Desc)
    (input : CodecDecode.Input) (source : BitVec 64) (readonly : Codec.Footprint)
    (address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  abi : Measure.ABI s ra t
  observed : ResultAt t.1.dmem
    (ResultFootprint readonly s.regs.rdi.toBitVec
      (CodecDecode.decode desc input (Measure.arenaState address capacity used)).effects)
    source s.regs.rdi.toBitVec
    (CodecDecode.decode desc input (Measure.arenaState address capacity used)).result
  effects : EffectsAt t.1.dmem
    (ResultFootprint readonly s.regs.rdi.toBitVec
      (CodecDecode.decode desc input (Measure.arenaState address capacity used)).effects)
    source (CodecDecode.decode desc input (Measure.arenaState address capacity used)).effects
  cursor : widthLoad t.1.dmem (s.regs.r8.toNat + 16) 8 =
    some (CodecDecode.decode desc input (Measure.arenaState address capacity used)).used
  usedBound : (CodecDecode.decode desc input
    (Measure.arenaState address capacity used)).used ≤ capacity.toNat
  header : widthLoad t.1.dmem s.regs.r8.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.r8.toNat + 8) 8 = some capacity.toNat
  descriptor : Codec.DescAt t.1.dmem readonly s.regs.rsi.toBitVec desc
  inputStored : Large.BytesAt t.1.dmem s.regs.rdx.toBitVec input.bytes
  mapping : SszX86.BitVector.Mapping.Extends s.dmem t.1.dmem
  frame : Codec.MemoryFrame s.dmem t.1.dmem
    (Writable s desc (CodecDecode.decode desc input (Measure.arenaState address capacity used)).effects)

end SszX86.CodecDeserialize
