import SszX86.HashContracts

namespace SszX86.Hash.Combine
open SszX86.WordNormalize

/-- The five arguments retained across all real helper calls. -/
def arguments (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    r14 := s.regs.r8, r15 := s.regs.rcx, r13 := s.regs.rdx,
    rbp := s.regs.rsi, rbx := s.regs.rdi}}

theorem arguments_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (arguments s, root + 29)) :
    Eventually (step e) P (s, root + 14) := by
  hash_combine_step 7 using hc
  hash_combine_step 8 using hc
  hash_combine_step 9 using hc
  hash_combine_step 10 using hc
  hash_combine_step 11 using hc
  word_simpa [arguments] using next

def leftCompressionArgs (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rdi := s.regs.r12, rsi := s.regs.rbp}}

theorem left_compression_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (leftCompressionArgs s, root + 198)) :
    Eventually (step e) P (s, root + 192) := by
  hash_combine_step 34 using hc
  hash_combine_step 35 using hc
  word_simpa [leftCompressionArgs] using next

def rightCompressionArgs (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rdi := s.regs.r12, rsi := s.regs.r15}}

theorem right_compression_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (rightCompressionArgs s, root + 358)) :
    Eventually (step e) P (s, root + 352) := by
  hash_combine_step 73 using hc
  hash_combine_step 74 using hc
  word_simpa [rightCompressionArgs] using next

def leftCopyArgs (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8),
    rsi := s.regs.rbp, rdx := s.regs.r13}}

theorem left_copy_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (leftCopyArgs s, root + 228)) :
    Eventually (step e) P (s, root + 217) := by
  hash_combine_step 41 using hc
  hash_combine_step 42 using hc
  hash_combine_step 43 using hc
  word_simpa [leftCopyArgs] using next

def rightCopyArgs (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8),
    rsi := s.regs.r15, rdx := s.regs.r14}}

theorem right_copy_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (rightCopyArgs s, root + 388)) :
    Eventually (step e) P (s, root + 377) := by
  hash_combine_step 80 using hc
  hash_combine_step 81 using hc
  hash_combine_step 82 using hc
  word_simpa [rightCopyArgs] using next

def finalizeArgs (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8), rdi := s.regs.rbx}}

theorem finalize_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (finalizeArgs s, root + 407)) :
    Eventually (step e) P (s, root + 399) := by
  hash_combine_step 85 using hc
  hash_combine_step 86 using hc
  word_simpa [finalizeArgs] using next

/-- The buffered block is already in place: this block changes no memory. -/
def bufferCompressionArgs (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8), rdi := s.regs.r12}}

theorem buffer_compression_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (bufferCompressionArgs s, root + 317)) :
    Eventually (step e) P (s, root + 309) := by
  hash_combine_step 65 using hc
  hash_combine_step 66 using hc
  word_simpa [bufferCompressionArgs] using next

/-- Only dead arithmetic flags are hidden by a bounded register summary. -/
def leftAdvanced (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r13 := UInt64.ofBitVec (s.regs.r13.toBitVec - 64),
    rbp := UInt64.ofBitVec (s.regs.rbp.toBitVec + 64)}, status := flags}

def rightAdvanced (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r14 := UInt64.ofBitVec (s.regs.r14.toBitVec - 64),
    r15 := UInt64.ofBitVec (s.regs.r15.toBitVec + 64)}, status := flags}

theorem left_advance_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (leftAdvanced s flags, root + 211)) :
    Eventually (step e) P (s, root + 203) := by
  hash_combine_step 37 using hc
  hash_combine_step 38 using hc
  have subtract : -(64#64) = 18446744073709551552#64 := by decide
  word_simpa [leftAdvanced, BitVec.sub_eq_add_neg, subtract] using next _

theorem right_advance_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (rightAdvanced s flags, root + 371)) :
    Eventually (step e) P (s, root + 363) := by
  hash_combine_step 76 using hc
  hash_combine_step 77 using hc
  have subtract : -(64#64) = 18446744073709551552#64 := by decide
  word_simpa [rightAdvanced, BitVec.sub_eq_add_neg, subtract] using next _

def bufferAdvanced (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r15 := UInt64.ofBitVec (s.regs.r15.toBitVec + s.regs.rbp.toBitVec),
    r14 := UInt64.ofBitVec (s.regs.r14.toBitVec - s.regs.rbp.toBitVec)}, status := flags}

private theorem sub_register (a b : UInt64) :
    a - b = UInt64.ofBitVec (a.toBitVec - b.toBitVec) := rfl

theorem buffer_advance_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (bufferAdvanced s flags, root + 309)) :
    Eventually (step e) P (s, root + 303) := by
  hash_combine_step 63 using hc
  hash_combine_step 64 using hc
  word_simpa [bufferAdvanced, sub_register] using next _

/-- The actual JA flag condition is precisely at least one remaining block. -/
private theorem above63 (x : BitVec 64) :
    (decide (x.toNat < 63) = false ∧ (x - 63#64 == 0#64) = false) ↔
      64 ≤ x.toNat := by
  rw [Udivti3.zf_sub]
  simp only [decide_eq_false_iff_not]
  have same : x = 63#64 ↔ x.toNat = 63 := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact BitVec.eq_of_toNat_eq h
  rw [same]
  omega

theorem left_entry_test_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rdx.toNat < 64 then root + 217 else root + 192)) :
    Eventually (step e) P (s, root + 180) := by
  have target := hc.targets ("hash_combine_u217", 217) (by decide)
  hash_combine_step 31 using hc
  hash_combine_step 32 using hc
  simp only [StatusFlags.from_result, target, decide_eq_true_eq]
  split
  · rename_i branch
    have small : s.regs.rdx.toBitVec.toNat < 64 := by
      word_simpa [] using branch
    word_simpa [small, ↓reduceIte, Effects.All,
      show Int64.ofNat 217 = (217 : Int64) by rfl] using next _
  · rename_i branch
    have large : ¬s.regs.rdx.toBitVec.toNat < 64 := by
      word_simpa [] using branch
    hash_combine_step 33 using hc
    word_simpa [large, ↓reduceIte] using next _

theorem right_entry_test_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r14.toNat < 64 then root + 377 else root + 352)) :
    Eventually (step e) P (s, root + 331) := by
  have target := hc.targets ("hash_combine_u377", 377) (by decide)
  hash_combine_step 69 using hc
  hash_combine_step 70 using hc
  simp only [StatusFlags.from_result, target, decide_eq_true_eq]
  split
  · rename_i branch
    have small : s.regs.r14.toBitVec.toNat < 64 := by
      word_simpa [] using branch
    word_simpa [small, ↓reduceIte, Effects.All,
      show Int64.ofNat 377 = (377 : Int64) by rfl] using next _
  · rename_i branch
    have large : ¬s.regs.r14.toBitVec.toNat < 64 := by
      word_simpa [] using branch
    hash_combine_step 71 using hc
    hash_combine_step 72 using hc
    word_simpa [large, ↓reduceIte] using next _

theorem left_loop_test_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if 64 ≤ s.regs.r13.toNat then root + 192 else root + 217)) :
    Eventually (step e) P (s, root + 211) := by
  have target := hc.targets ("hash_combine_u192", 192) (by decide)
  hash_combine_step 39 using hc
  hash_combine_step 40 using hc
  simp only [StatusFlags.from_result, target]
  split
  · rename_i branch
    have enough : 64 ≤ s.regs.r13.toBitVec.toNat := by
      apply (above63 _).mp
      word_simpa [] using branch
    word_simpa [enough, ↓reduceIte, Effects.All,
      show Int64.ofNat 192 = (192 : Int64) by rfl] using next _
  · rename_i branch
    have short : ¬64 ≤ s.regs.r13.toBitVec.toNat := by
      intro enough
      apply branch
      word_simpa [] using (above63 _).mpr enough
    word_simpa [short, ↓reduceIte, Effects.All] using next _

theorem right_loop_test_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if 64 ≤ s.regs.r14.toNat then root + 352 else root + 377)) :
    Eventually (step e) P (s, root + 371) := by
  have target := hc.targets ("hash_combine_u352", 352) (by decide)
  hash_combine_step 78 using hc
  hash_combine_step 79 using hc
  simp only [StatusFlags.from_result, target]
  split
  · rename_i branch
    have enough : 64 ≤ s.regs.r14.toBitVec.toNat := by
      apply (above63 _).mp
      word_simpa [] using branch
    word_simpa [enough, ↓reduceIte, Effects.All,
      show Int64.ofNat 352 = (352 : Int64) by rfl] using next _
  · rename_i branch
    have short : ¬64 ≤ s.regs.r14.toBitVec.toNat := by
      intro enough
      apply branch
      word_simpa [] using (above63 _).mpr enough
    word_simpa [short, ↓reduceIte, Effects.All] using next _

end SszX86.Hash.Combine
