import SszX86.CodecMeasureCore
import SszX86.CodecMeasureImpl
import SszX86.CodecMeasurePartsImpl
import SszX86.CodecMeasureChildImpl
import SszX86.CodecIsFixedImpl
import SszX86.CodecPlanSingletonImpl
import SszX86.CodecStack
import SszX86.MeasureOwned
import SszX86.NatAddMemory
import SszX86.BitVectorMapping

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative UintCodec

/-- The recursive allowance uses finite descriptor nesting, never Nat magnitudes
or schema validity. The 280-byte leaf allowance includes the existing BSR helper;
Nat::add needs48, and the actual codec activations/CALL slots are in each layer. -/
def stackBytes (desc : SszNative.Codec.Desc) : Nat := Codec.descriptorStackBytes desc 280

def isFixedOffset : Int := measurePartsOffset + CodecMeasureParts.isFixedOffset

def measureChildOffset : Int := measurePartsOffset + CodecMeasureParts.measureChildOffset

/-- Every helper premise is fetch/target ownership in the same linked image,
not an assumed execution or a promised recursive result. -/
structure HelpersAt (e : Executable) (base : Int64) : Prop where
  primitive : Measure.HelpersAt e base
  parts : CodecMeasureParts.CodeAt e (base + Int64.ofInt measurePartsOffset)
  child : CodecMeasureChild.CodeAt e (base + Int64.ofInt measureChildOffset)
  classifier : CodecIsFixed.CodeAt e (base + Int64.ofInt isFixedOffset)
  add : NatAdd.CodeAt e (base + Int64.ofInt natAddOffset)
  singleton : CodecPlanSingleton.CodeAt e (base + Int64.ofInt planSingletonOffset)

/-- Potential writes used only for original ownership, not as a claim that all
reserved bytes are initialized or touched. The postcondition below is narrower. -/
def Available (s : MachineData) (desc : SszNative.Codec.Desc)
    (address capacity used : BitVec 64) : Codec.Footprint := fun a =>
  Codec.InSpan a s.regs.rdi.toBitVec 72 ∨
  Codec.InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨
  Codec.InSpan a (address + used) (capacity.toNat - used.toNat) ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Original measure ABI and physical caller ownership for all thirteen shapes.
The immutable graph may share any readonly storage, including the used arena
prefix. No schema, result, branch, successful allocation or future call is assumed. -/
structure Owned (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (readonly : Codec.Footprint)
    (address capacity used ra : BitVec 64) (retain : Bool) : Prop where
  physical : value.Physical
  descriptor : Codec.DescAt s.dmem readonly s.regs.rsi.toBitVec desc
  valueStored : Codec.ValueAt s.dmem readonly s.regs.rdx.toBitVec value
  descriptorMapped : Large.Mapped s.dmem s.regs.rsi.toBitVec 40
  valueMapped : Large.Mapped s.dmem s.regs.rdx.toBitVec 48
  retainFlag : s.regs.r8.toBitVec.setWidth 8 = BitVec.ofNat 8 (if retain then 1 else 0)
  arena : Measure.ArenaAt s.dmem s.regs.rcx.toBitVec address capacity used
  usedBound : used.toNat ≤ capacity.toNat
  arenaBound : address.toNat + capacity.toNat ≤ 2 ^ 64
  arenaNonzero : 0 < capacity.toNat → 0 < address.toNat
  arenaMapped : Large.Mapped s.dmem address capacity.toNat
  resultBound : s.regs.rdi.toNat + 72 ≤ 2 ^ 64
  resultAligned : s.regs.rdi.toNat % 8 = 0
  resultNonzero : 0 < s.regs.rdi.toNat
  resultMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 72
  headerBound : s.regs.rcx.toNat + 24 ≤ 2 ^ 64
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec (stackBytes desc)
  stackAligned : s.regs.rsp.toNat % 8 = 0
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  resultHeader : Large.Disjoint s.regs.rdi.toBitVec s.regs.rcx.toBitVec 72 24
  resultStack : Large.Disjoint s.regs.rdi.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) 72 (stackBytes desc + 8)
  headerStack : Large.Disjoint s.regs.rcx.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) 24 (stackBytes desc + 8)
  freeResult : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 72
  freeHeader : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rcx.toNat 24
  freeStack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - stackBytes desc) (stackBytes desc + 8)
  readonlyDisjoint : ∀ a, readonly a → ¬ Available s desc address capacity used a
  table : TableAt s.dmem base
  tableReadonly : ∀ a, Codec.InSpan a (tableAddress base) 52 → readonly a
  classifierTable : CodecIsFixed.TableAt s.dmem (base + Int64.ofInt isFixedOffset)
  classifierTableReadonly : ∀ a,
    Codec.InSpan a (CodecIsFixed.tableAddress (base + Int64.ofInt isFixedOffset)) 48 → readonly a

/-- Only successful initializer/limb writes enter the arena write frame. Mere
reservation does not permit any mutation of an unused Plan suffix or padding gap. -/
def Writable (s : MachineData) (desc : SszNative.Codec.Desc)
    (effects : List SszNative.CodecMeasure.Effect) : Codec.Footprint := fun a =>
  Codec.InSpan a s.regs.rdi.toBitVec 72 ∨ EffectsWrite effects a ∨
  Codec.InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Full native return: shared exact errors/results/resources, recursive retained
Plan storage, caller ABI, mapping preservation and byte-exact outside-write frame. -/
structure Post (s : MachineData) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (readonly : Codec.Footprint)
    (address capacity used ra : BitVec 64) (retain : Bool) (t : MachineState) : Prop where
  abi : Measure.ABI s ra t
  observed : ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).result
  active : ActiveResultAt t.1.dmem
    (ResultFootprint readonly s.regs.rdi.toBitVec
      (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).effects)
    s.regs.rdi.toBitVec
    (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).result
  effects : EffectsAt t.1.dmem
    (ResultFootprint readonly s.regs.rdi.toBitVec
      (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).effects)
    (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).effects
  cursor : widthLoad t.1.dmem (s.regs.rcx.toNat + 16) 8 =
    some (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).used
  usedBound : (SszNative.CodecMeasure.measure desc value
    (Measure.arenaState address capacity used) retain).used ≤ capacity.toNat
  header : widthLoad t.1.dmem s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.rcx.toNat + 8) 8 = some capacity.toNat
  descriptor : Codec.DescAt t.1.dmem readonly s.regs.rsi.toBitVec desc
  valueStored : Codec.ValueAt t.1.dmem readonly s.regs.rdx.toBitVec value
  mapping : BitVector.Mapping.Extends s.dmem t.1.dmem
  frame : Codec.MemoryFrame s.dmem t.1.dmem
    (Writable s desc
      (SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) retain).effects)

end SszX86.CodecMeasure
