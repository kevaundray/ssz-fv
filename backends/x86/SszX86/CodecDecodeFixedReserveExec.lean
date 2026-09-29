import SszX86.CodecDecodeFixedImpl
import SszX86.CodecDecodeFixedReserveMath
import SszX86.DelimitedCore

namespace SszX86.CodecDecodeFixed
open Kraken.X64.Parser
open SszX86.UintCodec
open SszNative

macro "codec_value_reserve_step " row:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : SszX86.CodecDecodeFixed.programChunk1[$row]'(by decide) ∈
       SszX86.CodecDecodeFixed.program := by
     have localMember := List.getElem_mem
       (l := SszX86.CodecDecodeFixed.programChunk1) (n := $row) (by decide)
     simp only [SszX86.CodecDecodeFixed.program, List.mem_append,
       localMember, or_true, true_or]
   have fetched := SszX86.CodecDecodeFixed.step_at _ _ $hc
     (SszX86.CodecDecodeFixed.programChunk1[$row]'(by decide)) member
   simp only [SszX86.CodecDecodeFixed.programChunk1,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecDecodeFixed.directives, SszX86.CodecDecodeFixed.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "codec_value_reserve_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

def valuePaddingWord (address : BitVec 64) : BitVec 64 :=
  ((address + 15#64) &&& ~~~15#64) - address

def reserveFlagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def reserveAddressed (s : MachineData) (arena address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec arena
      rdi := UInt64.ofBitVec address
      rdx := UInt64.ofBitVec used
      rsi := UInt64.ofBitVec (used + address)}
    status := flags}

def reserveAligned (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r15 := UInt64.ofBitVec ((s.regs.rsi.toBitVec + 15#64) &&& ~~~15#64)
      rcx := UInt64.ofBitVec (valuePaddingWord s.regs.rsi.toBitVec + s.regs.rdx.toBitVec)}
    status := flags}

def reserveEnded (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.rcx.toBitVec)}
    status := flags}

def reserveCapacity (s : MachineData) (arena : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rdx := UInt64.ofBitVec arena}, status := flags}

structure ReserveHeader (s : MachineData) (arena address capacity used : BitVec 64) : Prop where
  arena_load : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 320#64) 8 = some (arena.toNat : Int)
  address_load : Mem.loadInt s.dmem arena 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (arena + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (arena + 16#64) 8 = some (used.toNat : Int)

theorem reserve_address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (arena address capacity used : BitVec 64)
    (header : ReserveHeader s arena address capacity used) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (reserveAddressed s arena address used flags,
        if used.toNat + address.toNat < 2^64 then base + 287 else base + 77)) :
    Eventually (step e) P (s, base + 260) := by
  have target := hc.targets ("codec_decode_fixed_u77", 77) (by decide)
  codec_value_reserve_step 0 using hc
  codec_value_reserve_load header.arena_load
  codec_value_reserve_step 1 using hc
  codec_value_reserve_load header.address_load
  codec_value_reserve_step 2 using hc
  codec_value_reserve_load header.used_load
  codec_value_reserve_step 3 using hc
  codec_value_reserve_step 4 using hc
  codec_value_reserve_step 5 using hc
  by_cases h : used.toNat + address.toNat < 2^64
  · have hn : ¬Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    simpa [h, reserveAddressed, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
  · have hn : Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    simpa [h, reserveAddressed, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _

/-- Literal CMP -16 accepts the last address whose +15 cannot overflow. -/
theorem reserve_rounding_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (reserveFlagged s flags,
        if s.regs.rsi.toNat + 15 < 2^64 then base + 297 else base + 77)) :
    Eventually (step e) P (s, base + 287) := by
  have target := hc.targets ("codec_decode_fixed_u77", 77) (by decide)
  codec_value_reserve_step 6 using hc
  codec_value_reserve_step 7 using hc
  by_cases h : s.regs.rsi.toNat + 15 < 2^64
  · have hn : ¬(18446744073709551600 ≤ s.regs.rsi.toNat ∧
        s.regs.rsi.toBitVec ≠ 18446744073709551600#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rsi.toNat = 18446744073709551600
      omega
    simpa [h, StatusFlags.from_result, hn, reserveFlagged, Effects.All] using next _
  · have hn : 18446744073709551600 ≤ s.regs.rsi.toNat ∧
        s.regs.rsi.toBitVec ≠ 18446744073709551600#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rsi.toNat = 18446744073709551600 at he'
      omega
    simpa [h, StatusFlags.from_result, hn, target, reserveFlagged, Effects.All] using next _

/-- AND -16 rounds the absolute pointer. SUB obtains padding, then ADD/JB
checks the cursor. No limb allocator's eight-byte mask is reused. -/
theorem reserve_alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (reserveAligned s flags,
        if (valuePaddingWord s.regs.rsi.toBitVec).toNat + s.regs.rdx.toNat < 2^64
        then base + 320 else base + 77)) :
    Eventually (step e) P (s, base + 297) := by
  have target := hc.targets ("codec_decode_fixed_u77", 77) (by decide)
  have raw : (valuePaddingWord s.regs.rsi.toBitVec).toNat =
      (18446744073709551616 - s.regs.rsi.toNat +
        ((s.regs.rsi.toNat + 15) % 18446744073709551616 &&& 18446744073709551600)) %
          18446744073709551616 := by simp [valuePaddingWord]
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          r15 := UInt64.ofBitVec ((s.regs.rsi.toBitVec + 15#64) &&& ~~~15#64)}
        status := flags}, base + 305) := by
    codec_value_reserve_step 10 using hc
    codec_value_reserve_step 11 using hc
    codec_value_reserve_step 12 using hc
    codec_value_reserve_step 13 using hc
    by_cases h : (valuePaddingWord s.regs.rsi.toBitVec).toNat + s.regs.rdx.toNat < 2^64
    · have hn : ¬Udivti3.radix ≤ s.regs.rdx.toNat +
          (valuePaddingWord s.regs.rsi.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at next
      rw [raw] at hn
      simpa [reserveAligned, valuePaddingWord, StatusFlags.from_result, hn,
        Effects.All, UInt64.add_comm] using next _
    · have hn : Udivti3.radix ≤ s.regs.rdx.toNat +
          (valuePaddingWord s.regs.rsi.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at next
      rw [raw] at hn
      simpa [reserveAligned, valuePaddingWord, StatusFlags.from_result, hn, target,
        Effects.All, UInt64.add_comm] using next _
  codec_value_reserve_step 8 using hc
  codec_value_reserve_step 9 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

theorem reserve_end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (reserveEnded s flags,
        if s.regs.rax.toNat + s.regs.rcx.toNat < 2^64 then base + 329 else base + 77)) :
    Eventually (step e) P (s, base + 320) := by
  have target := hc.targets ("codec_decode_fixed_u77", 77) (by decide)
  codec_value_reserve_step 14 using hc
  codec_value_reserve_step 15 using hc
  by_cases h : s.regs.rax.toNat + s.regs.rcx.toNat < 2^64
  · have hn : ¬Udivti3.radix ≤ s.regs.rcx.toNat + s.regs.rax.toNat := by dsimp [Udivti3.radix]; omega
    simpa [h, reserveEnded, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
  · have hn : Udivti3.radix ≤ s.regs.rcx.toNat + s.regs.rax.toNat := by dsimp [Udivti3.radix]; omega
    simpa [h, reserveEnded, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _

theorem reserve_capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (arena capacity : BitVec 64)
    (arenaLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 320#64) 8 = some (arena.toNat : Int))
    (capacityLoad : Mem.loadInt s.dmem (arena + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (reserveCapacity s arena flags,
        if s.regs.rax.toNat ≤ capacity.toNat then base + 347 else base + 77)) :
    Eventually (step e) P (s, base + 329) := by
  have target := hc.targets ("codec_decode_fixed_u77", 77) (by decide)
  codec_value_reserve_step 16 using hc
  codec_value_reserve_load arenaLoad
  codec_value_reserve_step 17 using hc
  codec_value_reserve_load capacityLoad
  codec_value_reserve_step 18 using hc
  by_cases h : s.regs.rax.toNat ≤ capacity.toNat
  · have hn : ¬(capacity.toNat ≤ s.regs.rax.toNat ∧ s.regs.rax.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rax.toNat = capacity.toNat
      omega
    simpa [h, StatusFlags.from_result, hn, reserveCapacity, Effects.All] using next _
  · have hn : capacity.toNat ≤ s.regs.rax.toNat ∧ s.regs.rax.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rax.toNat = capacity.toNat at he'
      omega
    simpa [h, StatusFlags.from_result, hn, target, reserveCapacity, Effects.All] using next _

/-- The unique write in the positive reservation prefix, before any Value field. -/
theorem reserve_commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (mapped : ∃ old, Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 16#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := Mem.storeInt s.dmem (s.regs.rdx.toBitVec + 16#64) 8
        s.regs.rax.toBitVec.toInt}, base + 351)) :
    Eventually (step e) P (s, base + 347) := by
  codec_value_reserve_step 19 using hc
  apply Delimited.store_cps
  · exact mapped
  · simpa only [Effects.All] using next

end SszX86.CodecDecodeFixed
