import SszX86.CodecDecodeListExec

set_option autoImplicit false

namespace SszX86.CodecDecodeList
open SszNative UintCodec

def SavedAt (m : DataMem) (sp : BitVec 64) (saved : BoolCodec.Saved) : Prop :=
  Mem.loadInt m (sp + 104#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 112#64) 8 = some (Int.ofBytes (wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 120#64) 8 = some (Int.ofBytes (wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 128#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 136#64) 8 = some (Int.ofBytes (wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 144#64) 8 = some (Int.ofBytes (wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 152#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returned (s : MachineData) (saved : BoolCodec.Saved) : MachineData :=
  {s with regs := {s.regs with
    rbx := UInt64.ofBitVec saved.rbx, r12 := UInt64.ofBitVec saved.r12,
    r13 := UInt64.ofBitVec saved.r13, r14 := UInt64.ofBitVec saved.r14,
    r15 := UInt64.ofBitVec saved.r15, rbp := UInt64.ofBitVec saved.rbp,
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 160#64)},
    status := Udivti3.addFlags 104#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "codec_list_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (codec_list_step1 $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

theorem epilogue (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : BoolCodec.Saved)
    (stored : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop) (post : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 328) := by
  rcases stored with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  codec_list_step1 6 using hc
  codec_list_pop 7 using hc word hrbx
  codec_list_pop 8 using hc word hr12
  codec_list_pop 9 using hc word hr13
  codec_list_pop 10 using hc word hr14
  codec_list_pop 11 using hc word hr15
  codec_list_pop 12 using hc word hrbp
  codec_list_pop 13 using hc word hrip
  have carry :
      ((s.regs.rsp.toBitVec + 104#64).unsigned !=
        (104#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 104 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 104#64 s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 152 = 160 by decide] using (Eventually.done _ post)

/-- The stack relation follows from the six executed pushes and the original
return slot, rather than an assumed future return frame. -/
theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (Dispatch.savedMem s) (s.regs.rsp.toBitVec - 152) (Dispatch.saved s ra) := by
  have original := Dispatch.saved_at s ra ret
  have offsets (a b : BitVec 64) (same : a - b = 208) :
      s.regs.rsp.toBitVec - 360 + a = s.regs.rsp.toBitVec - 152 + b := by bv_omega
  simpa only [BoolCodec.SavedAt, offsets 312 104 (by decide),
    offsets 320 112 (by decide), offsets 328 120 (by decide),
    offsets 336 128 (by decide), offsets 344 136 (by decide),
    offsets 352 144 (by decide), offsets 360 152 (by decide)] using original

/-- Output stores cannot modify any saved word when the original output is
separate from the physical saved activation. -/
theorem sequence_saved (m : DataMem) (out pointer count sp : BitVec 64)
    (saved : BoolCodec.Saved) (stored : SavedAt m sp saved)
    (separate : ∀ i < 56, ∀ j < 80,
      sp + BitVec.ofNat 64 (104 + i) ≠ out + BitVec.ofNat 64 j) :
    SavedAt (CodecDeserialize.sequenceMem m out pointer count) sp saved := by
  have preserved (off : Nat) (bound : off + 8 ≤ 56) :
      Mem.loadInt (CodecDeserialize.sequenceMem m out pointer count)
        (sp + BitVec.ofNat 64 (104 + off)) 8 =
      Mem.loadInt m (sp + BitVec.ofNat 64 (104 + off)) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply CodecDeserialize.sequence_frame
    intro writes
    rcases writes with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ |
      ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
    · exact separate (off + i) (by omega) j (by omega)
        (by simpa only [memmove_addr_add, Nat.add_assoc] using equal)
    · exact separate (off + i) (by omega) (16 + j) (by omega)
        (by simpa only [memmove_addr_add, Nat.add_assoc] using equal)
    · exact separate (off + i) (by omega) (24 + j) (by omega)
        (by simpa only [memmove_addr_add, Nat.add_assoc] using equal)
    · exact separate (off + i) (by omega) (32 + j) (by omega)
        (by simpa only [memmove_addr_add, Nat.add_assoc] using equal)
  rcases stored with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨(preserved 0 (by decide)).trans h0, (preserved 8 (by decide)).trans h1,
    (preserved 16 (by decide)).trans h2, (preserved 24 (by decide)).trans h3,
    (preserved 32 (by decide)).trans h4, (preserved 40 (by decide)).trans h5,
    (preserved 48 (by decide)).trans h6⟩

end SszX86.CodecDecodeList
