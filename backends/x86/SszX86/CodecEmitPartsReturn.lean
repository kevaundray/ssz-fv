import SszX86.CodecEmitPartsSteps
import SszX86.BoolReturn

namespace SszX86.CodecEmitParts
open BoolCodec UintCodec

/-- Six saved words and the caller return slot at their actual post-prologue
offsets. Local Result padding at bytes 24..95 is not observed by this predicate. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Mem.loadInt m (sp + 152#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 160#64) 8 = some (Int.ofBytes (wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 168#64) 8 = some (Int.ofBytes (wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 176#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 184#64) 8 = some (Int.ofBytes (wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 192#64) 8 = some (Int.ofBytes (wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 200#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returned (s : MachineData) (saved : Saved) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec saved.rbx
      r12 := UInt64.ofBitVec saved.r12
      r13 := UInt64.ofBitVec saved.r13
      r14 := UInt64.ofBitVec saved.r14
      r15 := UInt64.ofBitVec saved.r15
      rbp := UInt64.ofBitVec saved.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 208#64)}
    status := Udivti3.addFlags 152#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "codec_parts_pop " row:num " using " code:term " word " word:term : tactic => `(tactic|
  (codec_parts_step $row using $code
   simp [MachineData.load, Effects.All, ($word), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- The real ADD152, six POPs and RET restore the recursive caller's ABI. -/
theorem epilogue (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (saved : Saved) (stored : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (next : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 904) := by
  rcases stored with ⟨rbx, r12, r13, r14, r15, rbp, rip⟩
  codec_parts_step 217 using code
  codec_parts_pop 218 using code word rbx
  codec_parts_pop 219 using code word r12
  codec_parts_pop 220 using code word r13
  codec_parts_pop 221 using code word r14
  codec_parts_pop 222 using code word r15
  codec_parts_pop 223 using code word rbp
  codec_parts_pop 224 using code word rip
  have carry :
      ((s.regs.rsp.toBitVec + 152#64).unsigned !=
        (152#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 152 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 152#64 s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 200 = 208 by decide]
    using (Eventually.done _ next)

def successState (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rax.toBitVec + 64) 4 0}

/-- Success writes only its active status word. No error payload or padding is
read or initialized on this return path. -/
theorem status_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rax.toBitVec + 64) 4)
    (next : Eventually (step e) P (successState s, base + 904)) :
    Eventually (step e) P (s, base + 809) := by
  codec_parts_step 195 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero, show (64 : BitVec 64) = 64#64 by decide,
      show Width.W32.bytes = 4 by rfl] using
      Large.mapped_load s.dmem (s.regs.rax.toBitVec + 64) 4 0 4 mapped (by decide)
  codec_parts_step 196 using code
  simpa only [Effects.All, successState, show (64 : BitVec 64) = 64#64 by decide,
    show Width.W32.bytes = 4 by rfl, show (0#32).toInt = 0 by decide] using next

def lengthState (s : MachineData) (result : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec result},
    dmem := Mem.storeInt s.dmem result 8 s.regs.rbx.toBitVec.toInt}

/-- The sequential loop publishes its accumulated position through the original
sret pointer spilled at localSP+8. -/
theorem length_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (result : BitVec 64) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (result.toNat : Int))
    (mapped : Large.Mapped s.dmem result 8)
    (next : Eventually (step e) P (lengthState s result, base + 809)) :
    Eventually (step e) P (s, base + 801) := by
  codec_parts_step 193 using code
  codec_parts_load pointer
  codec_parts_step 194 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using Large.mapped_load s.dmem result 8 0 8 mapped (by decide)
  simpa only [Effects.All, lengthState] using next

end SszX86.CodecEmitParts
