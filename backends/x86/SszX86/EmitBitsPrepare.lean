import SszX86.EmitBitsStart

namespace SszX86.Emit.Bits
open BoolCodec UintCodec

@[simp] private theorem take32_eq (v : BitVec 64) : v.take 32 = v.setWidth 32 := by
  rw [BitVec.take, ← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]

/-- The list path spills physical backing length before borrowing the prefix. -/
def listLengthSaved (s : MachineData) (length : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rcx := UInt64.ofBitVec length}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8) 8 length.toInt}

theorem list_length_save (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 24) 8 = some (length.toNat : Int))
    (writable : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (listLengthSaved s length, base + 462)) :
    Eventually (step e) P (s, base + 452) := by
  change Mem.loadInt s.dmem (s.regs.r12.toBitVec + 24#64) 8 = some (length.toNat : Int) at loaded
  emit_step 77 using hc
  simp only [MachineData.load]
  rw [loaded]
  simp only [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  emit_step 78 using hc
  apply Delimited.store_cps
  · exact writable
  simpa [listLengthSaved, Effects.All] using next

theorem list_backing_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (fits : s.regs.r13.toNat ≤ s.regs.rcx.toNat) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 471)) :
    Eventually (step e) P (s, base + 462) := by
  have notBelow : ¬ s.regs.rcx.toNat < s.regs.r13.toNat := Nat.not_lt.mpr fits
  emit_step 79 using hc
  emit_step 80 using hc
  simpa [StatusFlags.from_result, Udivti3.cf_sub, notBelow, Effects.All] using next _

def listLowSaved (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with
      r15 := s.regs.r9
      rbp := UInt64.ofBitVec ((s.regs.rax.toBitVec.take 32).setWidth 64)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 16) 8 s.regs.rax.toBitVec.toInt}

theorem list_low_save (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (writable : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (listLowSaved s, base + 481)) :
    Eventually (step e) P (s, base + 471) := by
  emit_step 81 using hc
  emit_step 82 using hc
  apply Delimited.store_cps
  · exact writable
  emit_step 83 using hc
  simpa [listLowSaved, Effects.All] using next

def remainderState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbp := UInt64.ofBitVec (((s.regs.rbp.toBitVec.take 32) &&& 7#32).setWidth 64)}
    status := flags}

theorem list_remainder (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (remainderState s flags, base + 484)) :
    Eventually (step e) P (s, base + 481) := by
  emit_step 84 using hc
  constructor
  all_goals simpa [remainderState, Effects.All] using next _

def listCopyReady (s : MachineData) (src : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    r12 := UInt64.ofBitVec src
    rdi := s.regs.r14
    rsi := UInt64.ofBitVec src
    rdx := s.regs.r13}}

theorem list_copy_ready (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (src : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (src.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (listCopyReady s src, base + 498)) :
    Eventually (step e) P (s, base + 484) := by
  change Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 = some (src.toNat : Int) at loaded
  emit_step 85 using hc
  simp only [MachineData.load]
  rw [loaded]
  simp only [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  emit_step 86 using hc
  emit_step 87 using hc
  emit_step 88 using hc
  simpa [listCopyReady, Effects.All] using next

def vectorLowSaved (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8) 8 s.regs.rax.toBitVec.toInt}

theorem vector_low_save (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (writable : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (vectorLowSaved s, base + 701)) :
    Eventually (step e) P (s, base + 696) := by
  emit_step 142 using hc
  apply Delimited.store_cps
  · exact writable
  simpa [vectorLowSaved, Effects.All] using next

theorem vector_length_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 24) 8 = some (length.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rbp := UInt64.ofBitVec length}}, base + 706)) :
    Eventually (step e) P (s, base + 701) := by
  change Mem.loadInt s.dmem (s.regs.r12.toBitVec + 24#64) 8 = some (length.toNat : Int) at loaded
  emit_step 143 using hc
  simp only [MachineData.load]
  rw [loaded]
  simpa only [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq] using next

theorem vector_backing_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (fits : s.regs.r13.toNat ≤ s.regs.rbp.toNat) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 715)) :
    Eventually (step e) P (s, base + 706) := by
  have notBelow : ¬ s.regs.rbp.toNat < s.regs.r13.toNat := Nat.not_lt.mpr fits
  emit_step 144 using hc
  emit_step 145 using hc
  simpa [StatusFlags.from_result, Udivti3.cf_sub, notBelow, Effects.All] using next _

def vectorCopyReady (s : MachineData) (src : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    r15 := s.regs.r9
    r12 := UInt64.ofBitVec src
    rdi := s.regs.r14
    rsi := UInt64.ofBitVec src
    rdx := s.regs.r13}}

theorem vector_copy_ready (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (src : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (src.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (vectorCopyReady s src, base + 732)) :
    Eventually (step e) P (s, base + 715) := by
  change Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 = some (src.toNat : Int) at loaded
  emit_step 146 using hc
  emit_step 147 using hc
  simp only [MachineData.load]
  rw [loaded]
  simp only [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  emit_step 148 using hc
  emit_step 149 using hc
  emit_step 150 using hc
  simpa [vectorCopyReady, Effects.All] using next

end SszX86.Emit.Bits
