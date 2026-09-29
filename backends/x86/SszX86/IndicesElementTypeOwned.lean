import SszX86.IndicesElementTypeDispatch
import SszX86.IndicesElementTypeOrdinal
import SszX86.IndicesElementTypeOutputMemory
import SszX86.IndicesElementTypeCopyInput
import SszX86.IndicesPathStorage
import SszX86.CodecStorageViews

namespace SszX86.IndicesElementType
open SszNative UintCodec

/-- Every premise observes the caller's original physical memory. The mapped
readonly footprint supplies opaque descriptor padding without choosing values.
Readonly inputs may alias one another; only the output must be separate. -/
structure Owned (s : MachineData) (base : Int64) (readonly : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (path : SszNative.Indices.PathStep) (ra : BitVec 64) : Prop where
  descriptor : Codec.DescAt s.dmem readonly s.regs.rsi.toBitVec desc
  pathStep : SszX86.Indices.Storage.PathStepAt s.dmem readonly s.regs.rdx.toBitVec path
  readonly_mapped : ∀ address, readonly address → ∃ byte, s.dmem.get? address = some byte
  readonly_separate : ∀ address, readonly address → ¬ Codec.InSpan address s.regs.rdi.toBitVec 72
  output_bound : s.regs.rdi.toNat + 72 ≤ 2^64
  output_mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 72
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  return_separate : ∀ i < 8, ¬ Codec.InSpan (s.regs.rsp.toBitVec + BitVec.ofNat 64 i)
    s.regs.rdi.toBitVec 72
  table : TableAt s.dmem base

/-- Success describes only native active result fields, or the full physical
copy of an originally represented child. Its otherwise opaque words are linked
to original source observations rather than filled with invented constants. -/
inductive ResultMemory (original : DataMem) (readonly : Codec.Footprint) (out : BitVec 64) :
    Except SszNative.Indices.Error SszNative.Codec.Desc → DataMem → Prop where
  | bool : ResultMemory original readonly out (.ok (.primitive .bool)) (boolMem original out)
  | uint : ResultMemory original readonly out (.ok (.primitive (.uint (.small 1))))
      (uintMem original out)
  | notSteppable : ResultMemory original readonly out (.error .notSteppable)
      (errorMem original out 0 0 56)
  | noSuchField (ordinal : NatOperand) :
      ResultMemory original readonly out (.error (.noSuchField ordinal))
        (errorMem original out ordinal.pointer ordinal.payload 57)
  | copied {pointer : BitVec 64} {desc : SszNative.Codec.Desc} (words : DescWords) :
      Codec.DescAt original readonly pointer desc → words.At original pointer →
      ResultMemory original readonly out (.ok desc) (copyMem original out words)

structure Returned (s : MachineData) (readonly : Codec.Footprint) (ra : BitVec 64)
    (result : Except SszNative.Indices.Error SszNative.Codec.Desc) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec ra
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx = s.regs.rbx
  rbp : t.1.regs.rbp = s.regs.rbp
  r12 : t.1.regs.r12 = s.regs.r12
  r13 : t.1.regs.r13 = s.regs.r13
  r14 : t.1.regs.r14 = s.regs.r14
  r15 : t.1.regs.r15 = s.regs.r15
  simd : t.1.zmms = s.zmms
  result : ResultMemory s.dmem readonly s.regs.rdi.toBitVec result t.1.dmem

/-- Any recursively borrowed child gets all five copy loads from the caller's
mapping, including inactive bytes absent from Codec.DescAt observations. -/
theorem Owned.child_words {s : MachineData} {base : Int64} {readonly : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {path : SszNative.Indices.PathStep} {ra pointer : BitVec 64}
    (owned : Owned s base readonly desc path ra) {child : SszNative.Codec.Desc}
    (stored : Codec.DescAt s.dmem readonly pointer child) :
    ∃ words : DescWords, words.At s.dmem pointer := by
  apply DescWords.of_mapped s.dmem pointer
  intro i inside
  exact owned.readonly_mapped _ (stored.span.covered _ ⟨i, inside, rfl⟩)

theorem Owned.output {s : MachineData} {base : Int64} {readonly : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {path : SszNative.Indices.PathStep} {ra : BitVec 64}
    (owned : Owned s base readonly desc path ra) : OutputMapped s := by
  intro i inside
  exact owned.output_mapped i (by omega)

theorem Owned.child_apart {s : MachineData} {base : Int64} {readonly : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {path : SszNative.Indices.PathStep} {ra pointer : BitVec 64}
    (owned : Owned s base readonly desc path ra) {child : SszNative.Codec.Desc}
    (stored : Codec.DescAt s.dmem readonly pointer child) :
    CodecPlanSingleton.Apart pointer 40 s.regs.rdi.toBitVec 68 := by
  intro i hi j hj equal
  apply owned.readonly_separate (pointer + BitVec.ofNat 64 i)
    (stored.span.covered _ ⟨i, hi, rfl⟩)
  exact ⟨j, by omega, equal⟩

theorem Owned.return_after {s : MachineData} {base : Int64} {readonly : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {path : SszNative.Indices.PathStep} {ra : BitVec 64}
    (owned : Owned s base readonly desc path ra) (m : DataMem) (bytes : Nat) (bound : bytes ≤ 64)
    (frame : Codec.MemoryFrame s.dmem m (SuccessWrites s.regs.rdi.toBitVec bytes)) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  apply retained_return s.dmem m s.regs.rdi.toBitVec s.regs.rsp.toBitVec ra bytes frame
  · intro i hi written
    apply owned.return_separate i hi
    rcases written with ⟨j, hj, equal⟩ | shifted
    · exact ⟨j, by omega, equal⟩
    · exact Emit.span_shift s.regs.rdi.toBitVec 64 4 72 (by decide) shifted
  · exact owned.return_load

theorem fields_index {m : DataMem} {readonly : Codec.Footprint} {pointer : BitVec 64}
    {fields : List (String × SszNative.Codec.Desc)}
    (stored : Codec.FieldsAt m readonly pointer fields) (i : Nat) (inside : i < fields.length) :
    ∃ child : BitVec 64,
      Mem.loadInt m (pointer + BitVec.ofNat 64 (24*i) + 16) 8 = some (child.toNat : Int) ∧
      Codec.DescAt m readonly child fields[i].2 := by
  induction fields generalizing pointer i with
  | nil => simp at inside
  | cons field rest ih =>
    rcases field with ⟨name, desc⟩
    obtain ⟨child, load, childStored, restStored⟩ := Codec.FieldsAt.cons stored
    cases i with
    | zero => exact ⟨child, by simpa using load.load, childStored⟩
    | succ i =>
      obtain ⟨selected, load, selectedStored⟩ := ih restStored i (by simpa using inside)
      refine ⟨selected, ?_, selectedStored⟩
      convert load using 1
      congr 2
      simp only [BitVec.ofNat_add, BitVec.ofNat_mul]
      bv_omega

end SszX86.IndicesElementType
