import SszX86.NatToU128Output
import SszX86.DelimitedMemory

namespace SszX86.NatToU128
open SszNative
open UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Read-only limbs may overlap each other and the incoming return slot. -/
def BorrowedApart (out : Nat) (capacity : Nat) : NatOperand → Prop
  | .small _ => True
  | .large p limbs => Body.Apart p.toNat (8 * limbs.length) out capacity

/-- A byte frame sufficient to transport any disjoint physical read. -/
def ByteFrame (before after : DataMem) (out capacity : Nat) : Prop :=
  ∀ a : BitVec 64, Body.Outside a.toNat out capacity → after.get? a = before.get? a

theorem narrow_load_preserved (before after : DataMem) (out capacity p count : Nat)
    (frame : ByteFrame before after out capacity) (bound : p + count ≤ 2^64)
    (apart : Body.Apart p count out capacity) :
    Mem.loadInt after (BitVec.ofNat 64 p) count =
      Mem.loadInt before (BitVec.ofNat 64 p) count := by
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  apply frame
  have within : p+i < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
  unfold Body.Outside Body.Apart at *
  omega

theorem narrow_width_preserved (before after : DataMem) (out capacity p count : Nat)
    (frame : ByteFrame before after out capacity) (bound : p + count ≤ 2^64)
    (apart : Body.Apart p count out capacity) :
    widthLoad after p count = widthLoad before p count := by
  unfold widthLoad
  rw [narrow_load_preserved before after out capacity p count frame bound apart]

theorem narrow_operand_preserved (before after : DataMem) (out capacity : Nat)
    (operand : NatOperand) (frame : ByteFrame before after out capacity)
    (stored : operand.At (widthLoad before)) (apart : BorrowedApart out capacity operand) :
    operand.At (widthLoad after) := by
  cases operand with
  | small limb => trivial
  | large p limbs =>
    obtain ⟨positive, aligned, bound, limbReads⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    have subApart : Body.Apart (p.toNat + 8*i.val) 8 out capacity := by
      change Body.Apart p.toNat (8*limbs.length) out capacity at apart
      have hi := i.isLt
      unfold Body.Apart at *
      omega
    rw [narrow_width_preserved before after out capacity (p.toNat + 8*i.val) 8
      frame (by have := i.isLt; omega) subApart]
    exact limbReads i

private theorem result_observe_disjoint (m : DataMem) (out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 32) (hb : b + k ≤ 32) (hs : a + n ≤ b ∨ b + k ≤ a) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      observe m out a n := by
  unfold observe
  rw [load_store_disjoint _ _ _ _ _ _ (by intro i hi j hj; bv_omega)]

private theorem result_observe_same (m : DataMem) (out : BitVec 64)
    (off count : Nat) (value : Int) (bound : count ≤ 2^64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 off) count value) out off count =
      some (value.take (8*count)).toNat := by
  rw [observe, load_store_same m _ count value bound]
  rfl

private theorem result_load_observe (m : DataMem) (out : BitVec 64) (off count : Nat) :
    widthLoad m (out.toNat + off) count = observe m out off count := by
  simp only [widthLoad, observe, width_address]

private theorem result_load_observe_zero (m : DataMem) (out : BitVec 64) (count : Nat) :
    widthLoad m out.toNat count = observe m out 0 count := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

theorem narrow_signed64_nat (value : BitVec 64) :
    (value.toInt.take 64).toNat = value.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

macro "natu128_result_reads" : tactic => `(tactic|
  (simp (disch := first | assumption | omega | decide) only
     [noneMem, someMem, result_load_observe, result_load_observe_zero,
      result_observe_disjoint, observe_store64, result_observe_same,
      Nat.reduceAdd, Nat.reduceMul, narrow_signed64_nat]
   try decide))

theorem result_observed (m : DataMem) (out : BitVec 64) (result : Option (BitVec 128)) :
    NatNarrow.U128ResultAt (widthLoad (resultMem m out result)) out.toNat result := by
  cases result with
  | none =>
    change widthLoad (noneMem m out) out.toNat 8 = some 0 ∧
      widthLoad (noneMem m out) (out.toNat+8) 8 = some 0
    constructor <;> natu128_result_reads
  | some value =>
    change widthLoad (someMem m out value) out.toNat 8 = some 1 ∧
      widthLoad (someMem m out value) (out.toNat+8) 8 = some 0 ∧
      widthLoad (someMem m out value) (out.toNat+16) 8 = some (value.setWidth 64).toNat ∧
      widthLoad (someMem m out value) (out.toNat+24) 8 =
        some ((value >>> (64 : Nat)).setWidth 64).toNat
    refine ⟨?_, ?_, ?_, ?_⟩ <;> natu128_result_reads

def writtenBytes : Option (BitVec 128) → Nat
  | none => 16
  | some _ => 32

/-- Exact output write frame, including None's untouched payload. -/
def Frame (s : MachineData) (m : DataMem) (result : Option (BitVec 128)) : Prop :=
  ByteFrame s.dmem m s.regs.rdi.toNat (writtenBytes result)

theorem result_memory_frame (s : MachineData) (result : Option (BitVec 128))
    (bound : s.regs.rdi.toNat + 32 ≤ 2^64) :
    Frame s (resultMem s.dmem s.regs.rdi.toBitVec result) result := by
  intro a outside
  cases result with
  | none =>
    have away : ∀ i < 16, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i :=
      fun i hi => Body.outside_byte _ _ 16 i
        (by change s.regs.rdi.toNat + 16 ≤ 2^64; omega) outside hi
    simp (disch := first | assumption | omega | decide) only
      [resultMem, noneMem, store_frame (limit := 16)]
  | some value =>
    have away : ∀ i < 32, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i :=
      fun i hi => Body.outside_byte _ _ 32 i bound outside hi
    simp (disch := first | assumption | omega | decide) only
      [resultMem, someMem, store_frame (limit := 32)]

theorem result_byteFrame (s : MachineData) (result : Option (BitVec 128))
    (bound : s.regs.rdi.toNat + 32 ≤ 2^64) :
    ByteFrame s.dmem (resultMem s.dmem s.regs.rdi.toBitVec result) s.regs.rdi.toNat 32 := by
  intro a outside
  apply result_memory_frame s result bound a
  cases result <;> unfold Body.Outside at * <;> simp only [writtenBytes] <;> omega

/-- Only code and the physical caller-owned output, operand, and return slot. -/
structure Owned (s : MachineData) (operand : NatOperand) (ra : BitVec 64) : Prop where
  operand_pointer : s.regs.rsi.toBitVec = operand.pointer
  operand_payload : s.regs.rdx.toBitVec = operand.payload
  operand_at : operand.At (widthLoad s.dmem)
  operand_apart : BorrowedApart s.regs.rdi.toNat 32 operand
  output_bound : s.regs.rdi.toNat + 32 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  output_return : Body.Apart s.regs.rdi.toNat 32 s.regs.rsp.toNat 8

structure Post (s : MachineData) (operand : NatOperand) (ra : BitVec 64)
    (t : MachineState) : Prop where
  observed : NatNarrow.U128ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (NatNarrow.toU128 operand)
  returned : Delimited.Returned s ra t
  discriminant : t.1.regs.rax.toBitVec =
    if (NatNarrow.toU128 operand).isSome then 1 else 0
  frame : Frame s t.1.dmem (NatNarrow.toU128 operand)
  operand_at : operand.At (widthLoad t.1.dmem)
  memory : t.1.dmem = resultMem s.dmem s.regs.rdi.toBitVec (NatNarrow.toU128 operand)

theorem result_return_load (s : MachineData) (operand : NatOperand) (ra : BitVec 64)
    (owned : Owned s operand ra) (result : Option (BitVec 128)) :
    Mem.loadInt (resultMem s.dmem s.regs.rdi.toBitVec result) s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  have equal := narrow_load_preserved s.dmem
    (resultMem s.dmem s.regs.rdi.toBitVec result) s.regs.rdi.toNat 32 s.regs.rsp.toNat 8
    (result_byteFrame s result owned.output_bound) owned.return_bound owned.output_return.symm
  have address : BitVec.ofNat 64 s.regs.rsp.toNat = s.regs.rsp.toBitVec := by
    change BitVec.ofNat 64 s.regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [address, owned.return_load] using equal

theorem post_of_memory (s : MachineData) (operand : NatOperand) (ra : BitVec 64)
    (owned : Owned s operand ra) (t : MachineState)
    (memory : t.1.dmem = resultMem s.dmem s.regs.rdi.toBitVec (NatNarrow.toU128 operand))
    (returned : Delimited.Returned s ra t)
    (tag : t.1.regs.rax.toBitVec = if (NatNarrow.toU128 operand).isSome then 1 else 0) :
    Post s operand ra t := by
  refine ⟨?_, returned, tag, ?_, ?_, memory⟩
  · rw [memory]
    exact result_observed _ _ _
  · rw [memory]
    exact result_memory_frame s _ owned.output_bound
  · rw [memory]
    exact narrow_operand_preserved _ _ _ _ operand
      (result_byteFrame s _ owned.output_bound) owned.operand_at owned.operand_apart

end SszX86.NatToU128
