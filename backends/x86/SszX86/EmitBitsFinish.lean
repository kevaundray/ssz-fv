import SszX86.EmitBitsTailGuards
import SszX86.EmitBitsFinishMemory

namespace SszX86.Emit.Bits
open BoolCodec UintCodec
open UintCodec.Small (put replace8)

def alignedDelimiter (s : MachineData) : MachineData :=
  {put s .rdx (replace8 (UintCodec.Small.get s .rdx) 1#8) with regs :=
    {(put s .rdx (replace8 (UintCodec.Small.get s .rdx) 1#8)).regs with rsi := s.regs.r15}}

theorem aligned_delimiter (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (alignedDelimiter s, base + 1160)) :
    Eventually (step e) P (s, base + 1155) := by
  emit_step 257 using hc
  emit_step 258 using hc
  simpa [alignedDelimiter, put, replace8, UintCodec.Small.get, Reg64s.set64, Reg64s.get64,
    BitVec.replaceLow, BitVec.take, BitVec.drop, Effects.All] using next

theorem list_output_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (fits : s.regs.r13.toNat < s.regs.rsi.toNat) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 1169)) :
    Eventually (step e) P (s, base + 1160) := by
  have notBelow : ¬ s.regs.rsi.toNat < s.regs.r13.toNat := by omega
  have different : s.regs.rsi.toBitVec ≠ s.regs.r13.toBitVec := by
    intro equal
    have same := congrArg BitVec.toNat equal
    simp only [UInt64.toNat_toBitVec] at same
    omega
  emit_step 259 using hc
  emit_step 260 using hc
  simpa [StatusFlags.from_result, Udivti3.cf_sub, Udivti3.zf_sub,
    notBelow, different, Effects.All] using next _

def tailStored (s : MachineData) (byte : UInt8) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem (s.regs.r14.toBitVec + s.regs.r13.toBitVec) 1 byte.toBitVec.toInt}

theorem tail_store (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (byte : UInt8)
    (value : (if list then s.regs.rdx.toBitVec else s.regs.rax.toBitVec).take 8 = byte.toBitVec)
    (writable : ∃ old, Mem.loadInt s.dmem (s.regs.r14.toBitVec + s.regs.r13.toBitVec) 1 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (tailStored s byte, base + if list then 1173 else 793)) :
    Eventually (step e) P (s, base + if list then 1169 else 789) := by
  simp only [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] at value
  cases list
  · change s.regs.rax.toBitVec.setWidth 8 = byte.toBitVec at value
    emit_step 167 using hc
    apply Delimited.store_cps
    · exact writable
    change Eventually (step e) P
      ({s with
        dmem := Mem.storeInt s.dmem (s.regs.r14.toBitVec + s.regs.r13.toBitVec) 1 (s.regs.rax.toBitVec.setWidth 8).toInt},
        base + 793)
    rw [value]
    simpa only [Bool.false_eq_true, ite_false, tailStored] using next
  · change s.regs.rdx.toBitVec.setWidth 8 = byte.toBitVec at value
    emit_step 261 using hc
    apply Delimited.store_cps
    · exact writable
    change Eventually (step e) P
      ({s with
        dmem := Mem.storeInt s.dmem (s.regs.r14.toBitVec + s.regs.r13.toBitVec) 1 (s.regs.rdx.toBitVec.setWidth 8).toInt},
        base + 1173)
    rw [value]
    simpa only [Bool.true_eq, ite_true, tailStored] using next

def listIncremented (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r13 := s.regs.r13 + 1}, status := flags}

theorem list_increment (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (listIncremented s flags, base + 1176)) :
    Eventually (step e) P (s, base + 1173) := by
  emit_step 262 using hc
  simpa [listIncremented, Effects.All] using next _

inductive LengthSite where
  | list | vectorPartial | vectorAligned

def LengthSite.pc : LengthSite → Nat
  | .list => 1176 | .vectorPartial => 793 | .vectorAligned => 1275

def LengthSite.word (site : LengthSite) (s : MachineData) : BitVec 64 :=
  match site with
  | .list => s.regs.r13.toBitVec
  | .vectorPartial | .vectorAligned => s.regs.rbp.toBitVec

/-- The three real terminal paths converge at the actual success-status store,
not an invented RET or a helper-exit premise. -/
theorem length_store (e : Executable) (base : Int64) (hc : CodeAt e base)
    (site : LengthSite) (s : MachineData) (length : Nat)
    (storedWord : site.word s = BitVec.ofNat 64 length)
    (writable : ∃ old, Mem.loadInt s.dmem s.regs.rbx.toBitVec 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (lengthStored s length, base + 1593)) :
    Eventually (step e) P (s, base + Int64.ofNat site.pc) := by
  cases site
  · emit_step 263 using hc
    apply Delimited.store_cps
    · exact writable
    emit_step 264 using hc
    simpa [lengthStored, ← storedWord, LengthSite.word, Effects.All, Int64.add_assoc] using next
  · emit_step 168 using hc
    apply Delimited.store_cps
    · exact writable
    emit_step 169 using hc
    simpa [lengthStored, ← storedWord, LengthSite.word, Effects.All, Int64.add_assoc] using next
  · emit_step 265 using hc
    apply Delimited.store_cps
    · exact writable
    emit_step 266 using hc
    simpa [lengthStored, ← storedWord, LengthSite.word, Effects.All, Int64.add_assoc] using next

end SszX86.Emit.Bits
