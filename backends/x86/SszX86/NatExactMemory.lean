import SszX86.NatExactOutput
import SszX86.NatToU128Memory

namespace SszX86.NatExact
open SszNative
open UintCodec BoolCodec
open NatToU128 (ByteFrame BorrowedApart narrow_load_preserved narrow_width_preserved narrow_operand_preserved)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem result_observe_disjoint (m : DataMem) (out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 68) (hb : b + k ≤ 68) (hs : a + n ≤ b ∨ b + k ≤ a) :
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

macro "natexact_result_reads" : tactic => `(tactic|
  (simp (disch := first | assumption | omega | decide) only
     [successMem, failureMem, errorHeaderMem, result_load_observe, result_load_observe_zero,
      result_observe_disjoint, observe_store64, result_observe_same,
      Nat.reduceAdd, Nat.reduceMul, NatToU128.narrow_signed64_nat]
   try decide))

/-- Exactly the real status-only success write or complete 68-byte error write. -/
def Frame (s : MachineData) (m : DataMem) (success : Bool) : Prop :=
  if success then ByteFrame s.dmem m (s.regs.rdi.toNat + 64) 4
  else ByteFrame s.dmem m s.regs.rdi.toNat 68

theorem header_byteFrame (s : MachineData) (bound : s.regs.rdi.toNat + 68 ≤ 2^64) :
    ByteFrame s.dmem (errorHeaderMem s.dmem s.regs.rdi.toBitVec) s.regs.rdi.toNat 68 := by
  intro a outside
  have away : ∀ i < 68, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i :=
    fun i hi => Body.outside_byte _ _ 68 i bound outside hi
  simp (disch := first | assumption | omega | decide) only
    [errorHeaderMem, store_frame (limit := 68)]

theorem result_frame (s : MachineData) (expected : NatOperand) (actual : BitVec 64)
    (bound : s.regs.rdi.toNat + 68 ≤ 2^64) :
    Frame s (resultMem s.dmem s.regs.rdi.toBitVec expected actual)
      (NatNarrow.runExact expected actual) := by
  unfold resultMem Frame
  split
  · intro a outside
    have away : ∀ i < 4, a ≠ (s.regs.rdi.toBitVec + 64) + BitVec.ofNat 64 i := by
      intro i hi same
      change s.regs.rdi.toBitVec.toNat + 68 ≤ 2^64 at bound
      change Body.Outside a.toNat (s.regs.rdi.toBitVec.toNat + 64) 4 at outside
      unfold Body.Outside at outside
      bv_omega
    simpa only [successMem, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      store_frame s.dmem (s.regs.rdi.toBitVec + 64) a 4 0 4 0 (by decide) away
  · intro a outside
    have away : ∀ i < 68, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i :=
      fun i hi => Body.outside_byte _ _ 68 i bound outside hi
    simp (disch := first | assumption | omega | decide) only
      [failureMem, errorHeaderMem, store_frame (limit := 68)]

theorem result_byteFrame (s : MachineData) (expected : NatOperand) (actual : BitVec 64)
    (bound : s.regs.rdi.toNat + 68 ≤ 2^64) :
    ByteFrame s.dmem (resultMem s.dmem s.regs.rdi.toBitVec expected actual) s.regs.rdi.toNat 68 := by
  intro a outside
  have frame := result_frame s expected actual bound
  unfold Frame at frame
  split at frame
  · apply frame a
    unfold Body.Outside at *
    omega
  · exact frame a outside

structure Owned (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64) : Prop where
  actual_register : s.regs.rdx.toBitVec = actual
  expected_at : NatArithmetic.operandAt (widthLoad s.dmem) s.regs.rsi.toNat expected
  metadata_bound : s.regs.rsi.toNat + 16 ≤ 2^64
  metadata_apart : Body.Apart s.regs.rsi.toNat 16 s.regs.rdi.toNat 68
  operand_apart : BorrowedApart s.regs.rdi.toNat 68 expected
  output_bound : s.regs.rdi.toNat + 68 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  output_return : Body.Apart s.regs.rdi.toNat 68 s.regs.rsp.toNat 8

theorem metadata_preserved (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) (m : DataMem)
    (frame : ByteFrame s.dmem m s.regs.rdi.toNat 68) :
    widthLoad m s.regs.rsi.toNat 8 = some expected.pointer.toNat ∧
      widthLoad m (s.regs.rsi.toNat + 8) 8 = some expected.payload.toNat := by
  have apart := owned.metadata_apart
  have bound := owned.metadata_bound
  constructor
  · rw [narrow_width_preserved s.dmem m s.regs.rdi.toNat 68 s.regs.rsi.toNat 8
      frame (by omega) (by unfold Body.Apart at *; omega)]
    exact owned.expected_at.1
  · rw [narrow_width_preserved s.dmem m s.regs.rdi.toNat 68 (s.regs.rsi.toNat+8) 8
      frame (by omega) (by unfold Body.Apart at *; omega)]
    exact owned.expected_at.2.1

theorem header_reads (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) :
    Mem.loadInt (errorHeaderMem s.dmem s.regs.rdi.toBitVec) s.regs.rsi.toBitVec 8 =
      some (expected.pointer.toNat : Int) ∧
    Mem.loadInt (errorHeaderMem s.dmem s.regs.rdi.toBitVec) (s.regs.rsi.toBitVec+8) 8 =
      some (expected.payload.toNat : Int) := by
  obtain ⟨pointer, payload⟩ := metadata_preserved s expected actual ra owned _
    (header_byteFrame s owned.output_bound)
  change widthLoad _ s.regs.rsi.toBitVec.toNat 8 = _ at pointer
  change widthLoad _ (s.regs.rsi.toBitVec.toNat + 8) 8 = _ at payload
  constructor
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using widthLoad_eq _ _ _ _ pointer
  · change Mem.loadInt _ (s.regs.rsi.toBitVec + 8#64) 8 = _
    simpa only [width_address] using widthLoad_eq _ _ _ _ payload

theorem result_return_load (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) :
    Mem.loadInt (resultMem s.dmem s.regs.rdi.toBitVec expected actual) s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  have equal := narrow_load_preserved s.dmem
    (resultMem s.dmem s.regs.rdi.toBitVec expected actual) s.regs.rdi.toNat 68 s.regs.rsp.toNat 8
    (result_byteFrame s expected actual owned.output_bound) owned.return_bound owned.output_return.symm
  have address : BitVec.ofNat 64 s.regs.rsp.toNat = s.regs.rsp.toBitVec := by
    change BitVec.ofNat 64 s.regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [address, owned.return_load] using equal

theorem result_operand_at (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) :
    NatArithmetic.operandAt
      (widthLoad (resultMem s.dmem s.regs.rdi.toBitVec expected actual)) s.regs.rsi.toNat expected := by
  have frame := result_byteFrame s expected actual owned.output_bound
  obtain ⟨pointer, payload⟩ := metadata_preserved s expected actual ra owned _ frame
  exact ⟨pointer, payload, narrow_operand_preserved _ _ _ _ expected frame
    owned.expected_at.2.2 owned.operand_apart⟩

theorem result_observed (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) :
    NatNarrow.ExactResultAt
      (widthLoad (resultMem s.dmem s.regs.rdi.toBitVec expected actual)) s.regs.rdi.toNat expected actual := by
  change NatNarrow.ExactResultAt
    (widthLoad (resultMem s.dmem s.regs.rdi.toBitVec expected actual))
    s.regs.rdi.toBitVec.toNat expected actual
  have stored := (result_operand_at s expected actual ra owned).2.2
  cases outcome : NatNarrow.runExact expected actual with
  | false =>
    simp only [NatNarrow.ExactResultAt, resultMem, outcome, Bool.false_eq_true, ↓reduceIte] at stored ⊢
    refine ⟨?_, ?_, ⟨?_, ?_, stored⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [Nat.add_assoc, Nat.reduceAdd]) <;> natexact_result_reads
  | true =>
    simp only [NatNarrow.ExactResultAt, resultMem, outcome, ↓reduceIte]
    natexact_result_reads

structure Post (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (t : MachineState) : Prop where
  observed : NatNarrow.ExactResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat expected actual
  returned : Delimited.Returned s ra t
  status : t.1.regs.rax.toBitVec = if NatNarrow.runExact expected actual then 0 else 3
  frame : Frame s t.1.dmem (NatNarrow.runExact expected actual)
  original : NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rsi.toNat expected
  memory : t.1.dmem = resultMem s.dmem s.regs.rdi.toBitVec expected actual

theorem post_of_memory (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) (t : MachineState)
    (memory : t.1.dmem = resultMem s.dmem s.regs.rdi.toBitVec expected actual)
    (returned : Delimited.Returned s ra t)
    (status : t.1.regs.rax.toBitVec = if NatNarrow.runExact expected actual then 0 else 3) :
    Post s expected actual ra t := by
  refine ⟨?_, returned, status, ?_, ?_, memory⟩
  · rw [memory]
    exact result_observed s expected actual ra owned
  · rw [memory]
    exact result_frame s expected actual owned.output_bound
  · rw [memory]
    exact result_operand_at s expected actual ra owned

end SszX86.NatExact
