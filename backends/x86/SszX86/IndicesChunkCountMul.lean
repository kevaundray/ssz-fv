import SszX86.IndicesChunkCountExec
import SszX86.NatMulProofs

namespace SszX86.IndicesChunkCount
open SszNative UintCodec

def mulSetup (s : MachineData) (count : NatOperand) : MachineData :=
  {s with regs := {s.regs with
    r14 := s.regs.rdi, rax := UInt64.ofBitVec count.pointer,
    rdx := UInt64.ofBitVec count.payload, rdi := s.regs.rsp,
    rsi := UInt64.ofBitVec count.pointer, r9 := s.regs.rbx}}

/-- The unbounded-width path passes the original borrowed width unchanged.
The count is loaded only after the packing test has rejected that width. -/
theorem mul_setup_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (count : NatOperand)
    (pointer : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 =
      some (count.pointer.toNat : Int))
    (payload : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 =
      some (count.payload.toNat : Int)) (P : MachineState → Prop)
    (next : Eventually (step e) P (mulSetup s count, base + 503)) :
    Eventually (step e) P (s, base + 483) := by
  indices_count_step 121 using code
  indices_count_step 122 using code
  indices_count_load pointer
  indices_count_step 123 using code
  indices_count_load payload
  indices_count_step 124 using code
  indices_count_step 125 using code
  indices_count_step 126 using code
  simpa only [mulSetup] using next

def mulCallState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)},
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 (base + 508).toBitVec.toInt}

/-- The linked CALL is discharged by the immutable original multiplication
root, including its word-helper and memset closure. No multiplication-success
or future-execution hypothesis is used at this cut. -/
theorem mul_call_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (mulCode : NatMul.CodeAt e (base + Int64.ofInt natMulOffset))
    (wordCode : NatMulWord.CodeAt e ((base + Int64.ofInt natMulOffset) + 832))
    (memsetCode : NatMul.MemsetCall.MemsetCodeAt e
      ((base + Int64.ofInt natMulOffset) + 148928))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (owned : NatMul.Owned (mulCallState s base) left right address capacity used
      (base + 508).toBitVec) (P : MachineState → Prop)
    (next : ∀ t, NatMul.Post (mulCallState s base) left right address capacity used
      (base + 508).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 503) := by
  have body : Eventually (step e) P
      (mulCallState s base, base + Int64.ofInt natMulOffset) := by
    apply eventually_trans (step e)
      (NatMul.Post (mulCallState s base) left right address capacity used
        (base + 508).toBitVec)
    · exact NatMul.mul_correct e _ mulCode wordCode memsetCode
        (mulCallState s base) left right address capacity used (base + 508).toBitVec owned
    · exact next
  indices_count_step 127 using code
  apply Delimited.store_cps
  · exact slot
  · simpa [mulCallState, natMulOffset, Effects.All, Int64.add_assoc] using body

end SszX86.IndicesChunkCount
