import SszX86.CodecIsFixedPush
import SszX86.Udivti3Math

namespace SszX86.CodecIsFixed
open BoolCodec UintCodec

structure Saved where
  rbx : BitVec 64
  r14 : BitVec 64
  rip : BitVec 64

def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Mem.loadInt m (sp + 8#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 16#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 24#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returned (s : MachineData) (saved : Saved) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec saved.rbx
      r14 := UInt64.ofBitVec saved.r14
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 32#64)}
    status := Udivti3.addFlags 8#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "codec_is_fixed_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (codec_is_fixed_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- Both machine epilogues execute ADD8, POP RBX, POP R14, and the original
RET. No recursive helper return is postulated by this instruction theorem. -/
theorem epilogues (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (stored : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (post : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 53) ∧
      Eventually (step e) P (s, base + 124) := by
  rcases stored with ⟨rbx, r14, rip⟩
  have carry :
      ((s.regs.rsp.toBitVec + 8#64).unsigned !=
        (8#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 8 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 8#64 s.regs.rsp.toBitVec
  constructor
  · codec_is_fixed_step 18 using hc
    codec_is_fixed_pop 19 using hc word rbx
    codec_is_fixed_pop 20 using hc word r14
    codec_is_fixed_pop 21 using hc word rip
    simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
      BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
      show (8 : UInt64) + 24 = 32 by decide] using (Eventually.done _ post)
  · codec_is_fixed_step 39 using hc
    codec_is_fixed_pop 40 using hc word rbx
    codec_is_fixed_pop 41 using hc word r14
    codec_is_fixed_pop 42 using hc word rip
    simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
      BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
      show (8 : UInt64) + 24 = 32 by decide] using (Eventually.done _ post)

private theorem stored_word (m : DataMem) (p value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 value.toInt) p 8 =
      some (Int.ofBytes (wordBytes value)) := by
  rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
  exact load_store_same m p 8 value.toInt (by decide)

private theorem stack_apart (m : DataMem) (sp : BitVec 64) (a b : Nat)
    (ha : a ≤ 24) (hb : b ≤ 24) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) (v : Int) :
    Mem.loadInt (Mem.storeInt m (sp - BitVec.ofNat 64 b) 8 v)
      (sp - BitVec.ofNat 64 a) 8 = Mem.loadInt m (sp - BitVec.ofNat 64 a) 8 := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

/-- The saved ABI words are consequences of the actual entry stores. -/
theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 24)
      ⟨s.regs.rbx.toBitVec, s.regs.r14.toBitVec, ra⟩ := by
  have offsets (off : BitVec 64) :
      s.regs.rsp.toBitVec - 24 + off = s.regs.rsp.toBitVec - (24 - off) := by bv_omega
  simp only [SavedAt, offsets, BitVec.reduceSub]
  constructor
  · unfold savedMem
    simp only [show (8 : BitVec 64) = 8#64 by decide,
      show (16 : BitVec 64) = 16#64 by decide, show (24 : BitVec 64) = 24#64 by decide]
    rw [stack_apart _ s.regs.rsp.toBitVec 16 24 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  constructor
  · unfold savedMem
    simp only [show (8 : BitVec 64) = 8#64 by decide,
      show (16 : BitVec 64) = 16#64 by decide, show (24 : BitVec 64) = 24#64 by decide]
    rw [stack_apart _ s.regs.rsp.toBitVec 8 24 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 8 16 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  · simpa only [BitVec.sub_zero, ret] using saved_load s s.regs.rsp.toBitVec 8
      (by intro i hi j hj; bv_omega)

end SszX86.CodecIsFixed
