import SszX86.HashContracts

namespace SszX86.Hash.Finalize
open WordNormalize

abbrev get := UintCodec.Large.get
abbrev put := UintCodec.Large.put
abbrev putF := UintCodec.Large.putF
abbrev compare := UintCodec.Large.compare
abbrev subFlags (a b : BitVec 64) := UintCodec.Large.subFlags a b

theorem sub_word (a b : UInt64) :
    a - b = UInt64.ofBitVec (a.toBitVec - b.toBitVec) := rfl

def savedMem (s : MachineData) : DataMem :=
  Mem.storeInt (Mem.storeInt (Mem.storeInt s.dmem
    (s.regs.rsp.toBitVec - 8) 8 s.regs.r14.toBitVec.toInt)
    (s.regs.rsp.toBitVec - 16) 8 s.regs.rbx.toBitVec.toInt)
    (s.regs.rsp.toBitVec - 24) 8 s.regs.rax.toBitVec.toInt

def savedState (s : MachineData) : MachineData :=
  { s with regs := { s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 24) }
           dmem := savedMem s }

private theorem push_load (m : DataMem) (sp : BitVec 64) (offset : Nat)
    (hm : Mapped m (sp - 24) 24) (lo : 8 ≤ offset) (hi : offset ≤ 24) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 offset) 8 = some old := by
  have addr : sp - BitVec.ofNat 64 offset = (sp - 24) + BitVec.ofNat 64 (24 - offset) := by
    bv_omega
  rw [addr]
  exact UintCodec.Large.mapped_load m (sp - 24) 24 (24 - offset) 8 hm (by omega)

macro "finalize_push " row:num ", " off:num " using " hc:term ", " hm:term : tactic =>
  `(tactic|
    (hash_finalize_step $row using $hc
     try simp only [BitVec.sub_sub]
     apply Delimited.store_cps
     · apply push_load (offset := $off)
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
       · decide
     simp only [Effects.All]))

/-- The three physical PUSHes reserve the actual 24-byte local frame. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : Mapped s.dmem (s.regs.rsp.toBitVec - 24) 24)
    (next : Eventually (step e) P (savedState s, base + 4)) :
    Eventually (step e) P (s, base) := by
  have stackBits : s.regs.rsp.toBitVec - 8 - 8 - 8 = s.regs.rsp.toBitVec - 24 := by
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  finalize_push 0, 8 using hc, hm
  finalize_push 1, 16 using hc, hm
  finalize_push 2, 24 using hc, hm
  word_simpa [savedState, savedMem, Width.bytesv, Width.bytes, sub_word,
    BitVec.sub_sub, BitVec.reduceAdd, stackBits] using next

theorem capture_output_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (put s .rbx (get s .rdi), base + 7)) :
    Eventually (step e) P (s, base + 4) := by
  hash_finalize_step 3 using hc
  word_simpa [put, get, UintCodec.Large.put, UintCodec.Large.get,
    Reg64s.set64, Reg64s.get64, Effects.All] using next

/-- This first load is a full eight-byte load of the native buffered count. -/
theorem load_buffered_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64) (P : MachineState → Prop)
    (readValue : Mem.loadInt s.dmem (get s .rsi + 96) 8 = some (value.toNat : Int))
    (next : Eventually (step e) P (put s .rdi value, base + 11)) :
    Eventually (step e) P (s, base + 7) := by
  hash_finalize_step 4 using hc
  simp only [MachineData.load, Width.bytes, Width.bits, Effects.All, get, UintCodec.Large.get,
    Reg64s.get64, WordNormalize.bitvecNumeral] at readValue ⊢
  rw [readValue]
  word_simpa [put, UintCodec.Large.put, Reg64s.set64,
    Effects.All, Width.bits, BitVec.ofInt_natCast] using next

private theorem buffered_jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (safe : (!s.status.cf && !s.status.zf) = false)
    (next : Eventually (step e) P (s, base + 21)) :
    Eventually (step e) P (s, base + 15) := by
  have blocked : ¬ (s.status.cf = false ∧ s.status.zf = false) := by
    rintro ⟨carry, equal⟩
    rw [carry, equal] at safe
    cases safe
  hash_finalize_step 6 using hc
  word_simpa [blocked, ↓reduceIte, Effects.All] using next

private theorem overflow_jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (safe : (!s.status.cf && !s.status.zf) = false)
    (next : Eventually (step e) P (s, base + 56)) :
    Eventually (step e) P (s, base + 50) := by
  have blocked : ¬ (s.status.cf = false ∧ s.status.zf = false) := by
    rintro ⟨carry, equal⟩
    rw [carry, equal] at safe
    cases safe
  hash_finalize_step 15 using hc
  word_simpa [blocked, ↓reduceIte, Effects.All] using next

private theorem padding_jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (s, if s.status.cf || s.status.zf then base + 97 else base + 46)) :
    Eventually (step e) P (s, base + 44) := by
  have target := hc.targets ("hash_finalize_u97", 97) (by decide)
  hash_finalize_step 13 using hc
  simp only [target]
  split <;> rename_i branch
  all_goals word_simpa [Bool.or_eq_true, branch, ↓reduceIte, Effects.All,
    show Int64.ofNat 97 = (97 : Int64) by rfl] using next

theorem check_buffered_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (bound : (get s .rdi).toNat ≤ 63)
    (next : Eventually (step e) P (compare s (get s .rdi) 63, base + 21)) :
    Eventually (step e) P (s, base + 11) := by
  have safe : (!(subFlags (get s .rdi) 63).cf &&
      !(subFlags (get s .rdi) 63).zf) = false := by
    by_cases equal : get s .rdi = 63
    · simp [subFlags, UintCodec.Large.subFlags_zf, equal]
    · have less : (get s .rdi).toNat < 63 := by
        have ne : (get s .rdi).toNat ≠ 63 := by
          intro h
          exact equal (BitVec.eq_of_toNat_eq h)
        omega
      simp [subFlags, UintCodec.Large.subFlags_cf, less]
  have atBranch := buffered_jump_runs e base hc (compare s (get s .rdi) 63) P safe next
  hash_finalize_step 5 using hc
  word_simpa [compare, UintCodec.Large.compare, UintCodec.Large.subFlags,
    get, UintCodec.Large.get, Reg64s.get64, StatusFlags.from_result, Effects.All,
    BitVec.take, BitVec.signed, BitVec.zero, BitVec.toInt_sub,
    Udivti3.cf_sub, Udivti3.zf_sub,
    show BitVec.extractLsb' 0 4 (63#64) = 15#4 by decide,
    show (63#64).toNat = 63 by rfl,
    show (63#64).toInt = (63 : Int) by decide] using atBranch

def delimiterState (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with r14 := s.regs.rsi }
    dmem := Mem.storeInt s.dmem (get s .rsi + get s .rdi) 1 (-128) }

/-- The delimiter precedes the padding-branch test, exactly as in the image. -/
theorem delimiter_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapping : ∃ old, Mem.loadInt s.dmem (get s .rsi + get s .rdi) 1 = some old)
    (next : Eventually (step e) P (delimiterState s, base + 28)) :
    Eventually (step e) P (s, base + 21) := by
  hash_finalize_step 7 using hc
  hash_finalize_step 8 using hc
  apply Delimited.store_cps
  · word_simpa [get, UintCodec.Large.get, Reg64s.get64, Width.bytes] using mapping
  word_simpa [delimiterState, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All, Width.bytes, show (128#8).toInt = (-128 : Int) by decide] using next

theorem reload_buffered_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64) (P : MachineState → Prop)
    (readValue : Mem.loadInt s.dmem (get s .rsi + 96) 8 = some (value.toNat : Int))
    (next : Eventually (step e) P (put s .rax value, base + 32)) :
    Eventually (step e) P (s, base + 28) := by
  hash_finalize_step 9 using hc
  simp only [MachineData.load, Width.bytes, Width.bits, Effects.All, get, UintCodec.Large.get,
    Reg64s.get64, WordNormalize.bitvecNumeral] at readValue ⊢
  rw [readValue]
  word_simpa [put, UintCodec.Large.put, Reg64s.set64,
    Effects.All, Width.bits, BitVec.ofInt_natCast] using next

def advanceState (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with rdi := UInt64.ofBitVec (get s .rax + 1) }
    dmem := Mem.storeInt s.dmem (get s .rsi + 96) 8 (get s .rax + 1).toInt }

theorem advance_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapping : ∃ old, Mem.loadInt s.dmem (get s .rsi + 96) 8 = some old)
    (next : Eventually (step e) P (advanceState s, base + 40)) :
    Eventually (step e) P (s, base + 32) := by
  hash_finalize_step 10 using hc
  hash_finalize_step 11 using hc
  apply Delimited.store_cps
  · word_simpa [get, UintCodec.Large.get, Reg64s.get64, Width.bytes] using mapping
  word_simpa [advanceState, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All, Width.bytes, Width.bits] using next

/-- The branch follows the hardware's unsigned carry/equality observation. -/
theorem padding_branch_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (compare s (get s .rdi) 56,
        if (get s .rdi).toNat ≤ 56 then base + 97 else base + 46)) :
    Eventually (step e) P (s, base + 40) := by
  have branch : ((subFlags (get s .rdi) 56).cf ||
      (subFlags (get s .rdi) 56).zf) = decide ((get s .rdi).toNat ≤ 56) := by
    simp only [subFlags, UintCodec.Large.subFlags_cf, UintCodec.Large.subFlags_zf]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    have eq56 : get s .rdi = 56 ↔ (get s .rdi).toNat = 56 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact BitVec.eq_of_toNat_eq h
    rw [eq56]
    change (get s .rdi).toNat < 56 ∨ (get s .rdi).toNat = 56 ↔ _
    omega
  have atBranch : Eventually (step e) P (compare s (get s .rdi) 56, base + 44) := by
    apply padding_jump_runs e base hc (compare s (get s .rdi) 56) P
    simpa only [compare, UintCodec.Large.compare, branch, decide_eq_true_eq] using next
  hash_finalize_step 12 using hc
  word_simpa [compare, UintCodec.Large.compare, UintCodec.Large.subFlags,
    get, UintCodec.Large.get, Reg64s.get64, StatusFlags.from_result, Effects.All,
    BitVec.take, BitVec.signed, BitVec.zero, BitVec.toInt_sub,
    Udivti3.cf_sub, Udivti3.zf_sub,
    show BitVec.extractLsb' 0 4 (56#64) = 8#4 by decide,
    show (56#64).toNat = 56 by rfl,
    show (56#64).toInt = (56 : Int) by decide] using atBranch

theorem check_overflow_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (bound : (get s .rdi).toNat ≤ 64)
    (next : Eventually (step e) P (compare s (get s .rdi) 64, base + 56)) :
    Eventually (step e) P (s, base + 46) := by
  have safe : (!(subFlags (get s .rdi) 64).cf &&
      !(subFlags (get s .rdi) 64).zf) = false := by
    by_cases equal : get s .rdi = 64
    · simp [subFlags, UintCodec.Large.subFlags_zf, equal]
    · have less : (get s .rdi).toNat < 64 := by
        have ne : (get s .rdi).toNat ≠ 64 := by
          intro h
          exact equal (BitVec.eq_of_toNat_eq h)
        omega
      simp [subFlags, UintCodec.Large.subFlags_cf, less]
  have atBranch := overflow_jump_runs e base hc (compare s (get s .rdi) 64) P safe next
  hash_finalize_step 14 using hc
  word_simpa [compare, UintCodec.Large.compare, UintCodec.Large.subFlags,
    get, UintCodec.Large.get, Reg64s.get64, StatusFlags.from_result, Effects.All,
    BitVec.take, BitVec.signed, BitVec.zero, BitVec.toInt_sub,
    Udivti3.cf_sub, Udivti3.zf_sub,
    show BitVec.extractLsb' 0 4 (64#64) = 0#4 by decide,
    show (64#64).toNat = 64 by rfl,
    show (64#64).toInt = (64 : Int) by decide] using atBranch

def zeroSetup (s : MachineData) (count : BitVec 64) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with
      rdi := UInt64.ofBitVec (get s .rdi + get s .r14)
      rdx := UInt64.ofBitVec count
      rsi := 0 }
    status := flags }

/-- The first memset's zero count is legal at buffered=63. -/
theorem overflow_zero_setup_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (zeroSetup s (63 - get s .rax) flags, base + 69)) :
    Eventually (step e) P (s, base + 56) := by
  hash_finalize_step 16 using hc
  hash_finalize_step 17 using hc
  hash_finalize_step 18 using hc
  hash_finalize_step 19 using hc
  constructor
  all_goals word_simpa [zeroSetup, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All, sub_word] using next _

theorem final_zero_setup_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (zeroSetup s (56 - get s .rdi) flags, base + 110)) :
    Eventually (step e) P (s, base + 97) := by
  hash_finalize_step 26 using hc
  hash_finalize_step 27 using hc
  hash_finalize_step 28 using hc
  hash_finalize_step 29 using hc
  constructor
  all_goals word_simpa [zeroSetup, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All, sub_word] using next _

def resetState (s : MachineData) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with rdi := 0 }
    status := flags
    dmem := Mem.storeInt s.dmem (get s .r14 + 96) 8 0 }

theorem reset_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapping : ∃ old, Mem.loadInt s.dmem (get s .r14 + 96) 8 = some old)
    (next : ∀ flags, Eventually (step e) P (resetState s flags, base + 97)) :
    Eventually (step e) P (s, base + 87) := by
  hash_finalize_step 24 using hc
  apply Delimited.store_cps
  · word_simpa [get, UintCodec.Large.get, Reg64s.get64, Width.bytes] using mapping
  simp only [Effects.All]
  hash_finalize_step 25 using hc
  constructor
  all_goals word_simpa [resetState, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All, Width.bytes] using next _

def compressionSetup (s : MachineData) : MachineData :=
  { s with regs := { s.regs with
      rdi := UInt64.ofBitVec (get s .r14 + 64)
      rsi := s.regs.r14 } }

theorem overflow_compression_setup_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (compressionSetup s, base + 82)) :
    Eventually (step e) P (s, base + 75) := by
  hash_finalize_step 21 using hc
  hash_finalize_step 22 using hc
  word_simpa [compressionSetup, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All] using next

theorem final_compression_setup_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (compressionSetup s, base + 138)) :
    Eventually (step e) P (s, base + 131) := by
  hash_finalize_step 35 using hc
  hash_finalize_step 36 using hc
  word_simpa [compressionSetup, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All] using next

end SszX86.Hash.Finalize
