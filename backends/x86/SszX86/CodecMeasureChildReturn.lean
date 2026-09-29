import SszX86.CodecMeasureChildDecode
import SszX86.MeasureReturnMemory

namespace SszX86.CodecMeasureChild
open BoolCodec UintCodec

/-- The same six saved registers, below the child closure's original return slot. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Measure.SavedAt m (sp - 48) saved

def returned (s : MachineData) (saved : Saved) : MachineData :=
  {s with regs := {s.regs with
    rbx := UInt64.ofBitVec saved.rbx, r12 := UInt64.ofBitVec saved.r12,
    r13 := UInt64.ofBitVec saved.r13, r14 := UInt64.ofBitVec saved.r14,
    r15 := UInt64.ofBitVec saved.r15, rbp := UInt64.ofBitVec saved.rbp,
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 224)},
    status := Udivti3.addFlags 168 s.regs.rsp.toBitVec}

theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (Dispatch.savedMem s) (s.regs.rsp.toBitVec - 216) (Dispatch.saved s ra) := by
  simpa only [SavedAt, BitVec.sub_sub, BitVec.reduceAdd] using Measure.saved_at s ra ret

theorem savedAt_frame (before after : DataMem) (sp : BitVec 64) (saved : Saved)
    (writable : BitVec 64 → Prop) (frame : Measure.MemoryFrame before after writable)
    (untouched : ∀ i < 56, ¬ writable (sp + 168 + BitVec.ofNat 64 i))
    (stored : SavedAt before sp saved) : SavedAt after sp saved := by
  apply Measure.savedAt_frame before after (sp - 48) saved writable frame _ stored
  intro i hi
  have offset : sp - 48 + 216 + BitVec.ofNat 64 i = sp + 168 + BitVec.ofNat 64 i := by
    bv_omega
  rw [offset]
  exact untouched i hi

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "codec_measure_child_pop " row:num " using " code:term " word " stored:term : tactic => `(tactic|
  (codec_measure_child_step $row using $code
   simp [MachineData.load, Effects.All, ($stored), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- The genuine ADD168, six POPs and RET consume exactly the original return slot. -/
theorem epilogue (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (saved : Saved) (stored : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop) (next : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 622) := by
  have offset (n : BitVec 64) : s.regs.rsp.toBitVec - 48 + n =
      s.regs.rsp.toBitVec + (n - 48) := by bv_omega
  simp only [SavedAt, Measure.SavedAt, offset, BitVec.reduceSub] at stored
  rcases stored with ⟨rbx, r12, r13, r14, r15, rbp, rip⟩
  codec_measure_child_step 148 using code
  codec_measure_child_pop 149 using code word rbx
  codec_measure_child_pop 150 using code word r12
  codec_measure_child_pop 151 using code word r13
  codec_measure_child_pop 152 using code word r14
  codec_measure_child_pop 153 using code word r15
  codec_measure_child_pop 154 using code word rbp
  codec_measure_child_pop 155 using code word rip
  have carry : ((s.regs.rsp.toBitVec + 168).unsigned !=
      (168 : BitVec 64).unsigned + s.regs.rsp.toBitVec.unsigned) =
      decide (Udivti3.radix ≤ 168 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf (168 : BitVec 64) s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 216 = 224 by decide] using Eventually.done _ next

end SszX86.CodecMeasureChild
