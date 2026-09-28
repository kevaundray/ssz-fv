import SszX86.EmitBitsByteOps

namespace SszX86.Emit.Bits
open BoolCodec UintCodec

private theorem unequal_of_lt {a b : UInt64} (h : a.toNat < b.toNat) : a.toBitVec ≠ b.toBitVec := by
  intro equal
  have same := congrArg BitVec.toNat equal
  simp only [UInt64.toNat_toBitVec] at same
  omega

def listTested (s : MachineData) (af : Bool) : MachineData :=
  {s with
    status := StatusFlags.from_result (s.regs.rbp.toBitVec.take 32) {cf := false, af, of := false}}

theorem list_test (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ af, Eventually (step e) P (listTested s af,
      if s.regs.rbp.toBitVec.take 32 == 0#32 then base + 1155 else base + 512)) :
    Eventually (step e) P (s, base + 504) := by
  have target := hc.targets ("emit_u1155", 1155) (by decide)
  have branch (af : Bool) : Eventually (step e) P (listTested s af, base + 506) := by
    have selected := next af
    emit_step 91 using hc
    simp only [target]
    split <;> rename_i condition
    all_goals
      simp [listTested, StatusFlags.from_result] at condition
      simpa [listTested, StatusFlags.from_result, Effects.All, condition] using selected
  emit_step 90 using hc
  simpa [listTested] using And.intro (branch false) (branch true)

theorem vector_aligned (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (aligned : s.regs.rbp = s.regs.r13) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 1275)) :
    Eventually (step e) P (s, base + 738) := by
  have target := hc.targets ("emit_u1275", 1275) (by decide)
  emit_step 152 using hc
  emit_step 153 using hc
  simpa [aligned, StatusFlags.from_result, Effects.All, target] using next _

theorem vector_partial (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonaligned : s.regs.r13.toNat < s.regs.rbp.toNat) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 747)) :
    Eventually (step e) P (s, base + 738) := by
  have notBelow : ¬ s.regs.rbp.toNat < s.regs.r13.toNat := by omega
  have different := Ne.symm (unequal_of_lt nonaligned)
  emit_step 152 using hc
  emit_step 153 using hc
  simpa [StatusFlags.from_result, Udivti3.cf_sub, Udivti3.zf_sub,
    notBelow, different, Effects.All] using next _

theorem vector_output_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (fits : s.regs.r13.toNat < s.regs.r15.toNat) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 756)) :
    Eventually (step e) P (s, base + 747) := by
  have notBelow : ¬ s.regs.r15.toNat < s.regs.r13.toNat := by omega
  have different := Ne.symm (unequal_of_lt fits)
  emit_step 154 using hc
  emit_step 155 using hc
  simpa [StatusFlags.from_result, Udivti3.cf_sub, Udivti3.zf_sub,
    notBelow, different, Effects.All] using next _

theorem list_length_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (length.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rdx := UInt64.ofBitVec length}}, base + 517)) :
    Eventually (step e) P (s, base + 512) := by
  change Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (length.toNat : Int) at loaded
  emit_step 92 using hc
  simp only [MachineData.load]
  rw [loaded]
  simpa only [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq] using next

theorem list_partial_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonaligned : s.regs.r13.toNat < s.regs.rdx.toNat) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rsi := s.regs.r15}, status := flags}, base + 529)) :
    Eventually (step e) P (s, base + 517) := by
  have notBelow : ¬ s.regs.rdx.toNat < s.regs.r13.toNat := by omega
  have different := Ne.symm (unequal_of_lt nonaligned)
  emit_step 93 using hc
  emit_step 94 using hc
  simp [StatusFlags.from_result, Udivti3.zf_sub,
    notBelow, different, Effects.All]
  emit_step 95 using hc
  simpa [Effects.All] using next _

def byteLoaded (s : MachineData) (byte : UInt8) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (byte.toBitVec.setWidth 64)}}

theorem tail_byte_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (byte : UInt8)
    (loaded : Mem.loadInt s.dmem (s.regs.r12.toBitVec + s.regs.r13.toBitVec) 1 =
      some (byte.toNat : Int)) (P : MachineState → Prop)
    (next : Eventually (step e) P (byteLoaded s byte, base + if list then 534 else 761)) :
    Eventually (step e) P (s, base + if list then 529 else 756) := by
  cases list
  · emit_step 156 using hc
    simpa [MachineData.load, Effects.All, loaded, byteLoaded,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat] using next
  · emit_step 96 using hc
    simpa [MachineData.load, Effects.All, loaded, byteLoaded,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat] using next

def lastCompared (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (s.regs.r13.toBitVec + 1)}, status := flags}

theorem list_last_byte (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (last : s.regs.rdx.toBitVec = s.regs.r13.toBitVec + 1)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (lastCompared s flags, base + 543)) :
    Eventually (step e) P (s, base + 534) := by
  emit_step 97 using hc
  emit_step 98 using hc
  emit_step 99 using hc
  simpa [last, lastCompared, StatusFlags.from_result, Effects.All] using next _

theorem vector_last_byte (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (last : s.regs.rbp.toBitVec = s.regs.r13.toBitVec + 1)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (lastCompared s flags, base + 770)) :
    Eventually (step e) P (s, base + 761) := by
  emit_step 157 using hc
  emit_step 158 using hc
  emit_step 159 using hc
  simpa [last, lastCompared, StatusFlags.from_result, Effects.All] using next _

def remainderLoaded (s : MachineData) (low : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec low}}

theorem tail_count_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (low : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + if list then 16 else 8) 8 =
      some (low.toNat : Int)) (P : MachineState → Prop)
    (next : Eventually (step e) P (remainderLoaded s low, base + if list then 548 else 775)) :
    Eventually (step e) P (s, base + if list then 543 else 770) := by
  cases list
  · change Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (low.toNat : Int) at loaded
    emit_step 160 using hc
    simp only [MachineData.load]
    rw [loaded]
    simpa [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, remainderLoaded] using next
  · change Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (low.toNat : Int) at loaded
    emit_step 100 using hc
    simp only [MachineData.load]
    rw [loaded]
    simpa [Effects.All, Width.bits, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, remainderLoaded] using next

def tailRemainder (s : MachineData) (af : Bool) : MachineData :=
  {s with
    regs := {s.regs with rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec &&& 7#64)}
    status := StatusFlags.from_result (s.regs.rcx.toBitVec &&& 7#64) {cf := false, af, of := false}}

theorem tail_remainder_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (nonaligned : s.regs.rcx.toBitVec &&& 7#64 ≠ 0#64)
    (P : MachineState → Prop)
    (next : ∀ af, Eventually (step e) P (tailRemainder s af, base + if list then 554 else 781)) :
    Eventually (step e) P (s, base + if list then 548 else 775) := by
  cases list
  · have branch (af : Bool) : Eventually (step e) P (tailRemainder s af, base + 779) := by
      emit_step 162 using hc
      simpa [tailRemainder, StatusFlags.from_result, nonaligned, Effects.All] using next af
    emit_step 161 using hc
    exact ⟨branch false, branch true⟩
  · have branch (af : Bool) : Eventually (step e) P (tailRemainder s af, base + 552) := by
      emit_step 102 using hc
      simpa [tailRemainder, StatusFlags.from_result, nonaligned, Effects.All] using next af
    emit_step 101 using hc
    exact ⟨branch false, branch true⟩

end SszX86.Emit.Bits
