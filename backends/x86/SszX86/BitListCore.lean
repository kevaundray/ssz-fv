import SszX86.BitListImpl
import SszX86.DelimitedProofs
import SszX86.BoolReturn

namespace SszX86.BitList
open Kraken.X64.Parser
open SszNative UintCodec BoolCodec

macro "bitlist_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.BitList.step_at _ _ $hc
     (SszX86.BitList.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.BitList.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.BitList.program, SszX86.BitList.directives,
      Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

def optionMem (s : MachineData) (pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 32) 8 payload.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 24) 8 pointer.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec + 16) 8 1

def listState (s : MachineData) (pointer payload ra : BitVec 64) : MachineData :=
  { s with
    regs := {s.regs with
      rax := UInt64.ofBitVec pointer
      rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16)
      rcx := s.regs.r14
      r8 := s.regs.rbx
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt (optionMem s pointer payload) (s.regs.rsp.toBitVec - 8) 8 ra.toInt }

/-- The tail branch has already restored the caller's six registers. Its only
return slot is the original caller slot at bodySP+360. -/
def progressiveState (s : MachineData) (saved : Saved) : MachineData :=
  { s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec (s.regs.rbp.toBitVec + 8)
      rcx := s.regs.r14
      r8 := s.regs.rbx
      rbx := UInt64.ofBitVec saved.rbx
      r12 := UInt64.ofBitVec saved.r12
      r13 := UInt64.ofBitVec saved.r13
      r14 := UInt64.ofBitVec saved.r14
      r15 := UInt64.ofBitVec saved.r15
      rbp := UInt64.ofBitVec saved.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 360)}
    status := Udivti3.addFlags 312#64 s.regs.rsp.toBitVec }

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "bitlist_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (bitlist_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

theorem epilogue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (next : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 7720) := by
  rcases hs with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  bitlist_step 22 using hc
  bitlist_pop 23 using hc word hrbx
  bitlist_pop 24 using hc word hr12
  bitlist_pop 25 using hc word hr13
  bitlist_pop 26 using hc word hr14
  bitlist_pop 27 using hc word hr15
  bitlist_pop 28 using hc word hrbp
  bitlist_pop 29 using hc word hrip
  have carry :
      ((s.regs.rsp.toBitVec + 312#64).unsigned !=
        (312#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 312 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 312#64 s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 360 = 368 by decide]
    using (Eventually.done _ next)

theorem progressive_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (progressiveState s saved, base + Int64.ofInt delimitedOffset)) :
    Eventually (step e) P (s, base + Int64.ofNat progressiveEntry) := by
  rcases hs with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  bitlist_step 10 using hc
  bitlist_step 11 using hc
  bitlist_step 12 using hc
  bitlist_step 13 using hc
  bitlist_step 14 using hc
  bitlist_pop 15 using hc word hrbx
  bitlist_pop 16 using hc word hr12
  bitlist_pop 17 using hc word hr13
  bitlist_pop 18 using hc word hr14
  bitlist_pop 19 using hc word hr15
  bitlist_pop 20 using hc word hrbp
  bitlist_step 21 using hc
  have carry :
      ((s.regs.rsp.toBitVec + 312#64).unsigned !=
        (312#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 312 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 312#64 s.regs.rsp.toBitVec
  simpa [progressiveState, progressiveEntry, delimitedOffset, Udivti3.addFlags,
    BitVec.take, BitVec.signed, BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc,
    Int.add_comm, Nat.add_comm, carry, show (8 : UInt64) + 352 = 360 by decide] using next

theorem list_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hp : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (hn : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16) 8 = some (payload.toNat : Int))
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 48)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (listState s pointer payload (base + 1235).toBitVec,
        base + Int64.ofInt delimitedOffset)) :
    Eventually (step e) P (s, base + Int64.ofNat listEntry) := by
  have hp' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 =
      some (pointer.toNat : Int) := hp
  have hn' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
      some (payload.toNat : Int) := hn
  bitlist_step 0 using hc
  delimited_load hp'
  bitlist_step 1 using hc
  delimited_load hn'
  bitlist_step 2 using hc
  apply Delimited.store_cps
  · have h := Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 48 40 8 hm (by decide)
    rw [show s.regs.rsp.toBitVec - 8 + 40#64 = s.regs.rsp.toBitVec + 32#64 by bv_omega] at h
    simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt, Width.bytes,
      show BitVec.ofInt 64 32 = 32#64 by decide] using h
  simp only [Effects.All]
  bitlist_step 3 using hc
  apply Delimited.store_cps
  · simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, Width.bytes,
      show BitVec.ofInt 64 24 = 24#64 by decide]
    rw [← show s.regs.rsp.toBitVec - 8 + 32#64 = s.regs.rsp.toBitVec + 24#64 by bv_omega]
    apply Large.mapped_load (capacity := 48) («offset» := 32) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ hm
    · decide
  simp only [Effects.All]
  bitlist_step 4 using hc
  apply Delimited.store_cps
  · simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, Width.bytes,
      show BitVec.ofInt 64 16 = 16#64 by decide]
    rw [← show s.regs.rsp.toBitVec - 8 + 24#64 = s.regs.rsp.toBitVec + 16#64 by bv_omega]
    apply Large.mapped_load (capacity := 48) («offset» := 24) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ hm)
    · decide
  simp only [Effects.All]
  bitlist_step 5 using hc
  bitlist_step 6 using hc
  bitlist_step 7 using hc
  bitlist_step 8 using hc
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 48) (byteCount := 8)
    · repeat' first | exact hm | apply Large.mapped_store
    · decide
  simpa [listState, optionMem, delimitedOffset, Effects.All,
    BitVec.ofInt_add, BitVec.ofInt_toInt, Delimited.word_cast, Int64.add_assoc] using next

end SszX86.BitList
