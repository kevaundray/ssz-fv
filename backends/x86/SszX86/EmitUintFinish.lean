import SszX86.EmitUintInit

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open SszNative
open BoolCodec UintCodec
open UintCodec.Large (get)

def Writable (s : MachineData) (count : Nat) (address : BitVec 64) : Prop :=
  InSpan address s.regs.r14.toBitVec count ∨ InSpan address s.regs.rbx.toBitVec 8

structure OutputPost (original : MachineData) (number : NatOperand) (count : Nat)
    (base : Int64) (state : MachineState) : Prop where
  pc : state.2 = base + 1593
  body : BodyPost original (Limbs.bytes number.words count) state.1
  exactFrame : MemoryFrame original.dmem state.1.dmem (Writable original count)

/-- An original result slot remains mapped throughout the output-only prefix. -/
theorem result_mapped (original current : MachineData) (logicalWidth number : NatOperand)
    (count index : Nat) (owned : Owned original logicalWidth number count)
    (hprefix : Prefix original.dmem current.dmem original.regs.r14.toBitVec
      (Limbs.bytes number.words count) index) :
    ∃ old, Mem.loadInt current.dmem original.regs.rbx.toBitVec 8 = some old := by
  obtain ⟨old, hmap⟩ := Large.mapped_load original.dmem original.regs.rbx.toBitVec
    8 0 8 owned.result (by omega)
  refine ⟨old, ?_⟩
  rw [prefix_protected hprefix]
  · simpa using hmap
  · intro a inside output
    exact owned.apart a (by simpa only [Limbs.bytes, Array.size_ofFn] using output) inside

/-- The length MOV is the only result write before the shared status store. Its
output and result frame is stronger than BodyPost's permitted local-stack frame. -/
theorem finish_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original current : MachineData) (logicalWidth number : NatOperand) (count : Nat)
    (owned : Owned original logicalWidth number count)
    (stack : current.regs.rsp = original.regs.rsp)
    (result : current.regs.rbx = original.regs.rbx)
    (vector : current.zmms = original.zmms)
    (length : get current .rsi = BitVec.ofNat 64 count)
    (hprefix : Prefix original.dmem current.dmem original.regs.r14.toBitVec
      (Limbs.bytes number.words count) count) :
    Eventually (step e) (OutputPost original number count base) (current, base + 1147) := by
  have byteSize : (Limbs.bytes number.words count).size = count := by
    simp only [Limbs.bytes, Array.size_ofFn]
  have rawLength : current.regs.rsi.toBitVec = BitVec.ofNat 64 count := length
  have physical : count < 2 ^ 64 := by
    have bound := original.regs.r9.toBitVec.isLt
    have fits := owned.capacity
    simp only [UInt64.toNat_toBitVec] at bound
    omega
  have output : BytesAt current.dmem original.regs.r14.toBitVec (Limbs.bytes number.words count) :=
    prefix_output (by simpa only [byteSize] using hprefix)
  have frame : MemoryFrame original.dmem current.dmem (Writable original count) := by
    apply Bits.frame_mono (prefix_frame hprefix)
    intro a inside
    exact Or.inl inside
  have bodyFrame : MemoryFrame original.dmem current.dmem
      (BodyWritable original (Limbs.bytes number.words count).size) := by
    apply Bits.frame_mono frame
    intro a inside
    rcases inside with output | result
    · exact Or.inl (by simpa only [byteSize] using output)
    · exact Or.inr (Or.inl result)
  have apart : Large.Disjoint original.regs.r14.toBitVec original.regs.rbx.toBitVec
      (Limbs.bytes number.words count).size 8 := by
    intro i hi j hj equal
    exact owned.apart _ ⟨i, by simpa only [byteSize] using hi, rfl⟩
      ⟨j, hj, equal⟩
  have body := Bits.length_post original current (Limbs.bytes number.words count)
    (by simpa only [byteSize] using physical) stack result vector output bodyFrame apart
  have finished : OutputPost original number count base
      (Bits.lengthStored current count, base + 1593) := by
    refine ⟨rfl, ?_, ?_⟩
    · simpa only [byteSize] using body
    · apply Bits.frame_trans frame
      apply Bits.frame_mono (Bits.store_frame current.dmem current.regs.rbx.toBitVec 8 _)
      intro a inside
      exact Or.inr (by simpa only [result] using inside)
  apply length_runs e base hc current (OutputPost original number count base)
  · rw [result]
    exact result_mapped original current logicalWidth number count count owned hprefix
  · rw [rawLength]
    exact Eventually.done _ finished

/-- Full original padded operands are preserved by the stronger actual-write
frame, even when readonly objects alias each other or unused stack storage. -/
theorem natAt_preserved (before after : DataMem) (pair : BitVec 64) (operand : NatOperand)
    (writable : BitVec 64 → Prop) (frame : MemoryFrame before after writable)
    (stored : NatAt before pair operand)
    (readGuard : ∀ a, Borrowed pair operand a → ¬ writable a) : NatAt after pair operand := by
  have loadEq (p : BitVec 64) (byteCount : Nat)
      (inside : ∀ a, InSpan a p byteCount → Borrowed pair operand a) :
      Mem.loadInt after p byteCount = Mem.loadInt before p byteCount :=
    Bits.protected_load frame p byteCount (fun a span => readGuard a (inside a span))
  refine ⟨?_, ?_, ?_⟩
  · have stable := loadEq pair 8 (fun a span => Or.inl (Bits.span_subspan pair 0 8 16
      (by omega) (by simpa using span)))
    simpa only [widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq, stable] using stored.1
  · have stable := loadEq (pair + BitVec.ofNat 64 8) 8
      (fun a span => Or.inl (Bits.span_subspan pair 8 8 16 (by omega) span))
    simpa only [widthLoad, width_address, stable] using stored.2.1
  · cases operand with
    | small limb => trivial
    | large pointer limbs =>
      refine ⟨stored.2.2.1, stored.2.2.2.1, stored.2.2.2.2.1, ?_⟩
      intro i
      have stable := loadEq (pointer + BitVec.ofNat 64 (8 * i.val)) 8
        (fun a span => Or.inr (Bits.span_subspan pointer (8 * i.val) 8 (8 * limbs.length)
          (by have := i.isLt; omega) span))
      simpa only [widthLoad, width_address, stable] using stored.2.2.2.2.2 i

end SszX86.Emit.Uint
