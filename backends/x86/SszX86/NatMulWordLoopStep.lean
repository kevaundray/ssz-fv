import SszX86.NatMulWordMath
import SszX86.WordNormalize

namespace SszX86.NatMulWord
open UintCodec

def loopProductState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec * s.regs.rcx.toBitVec)
      rdx := UInt64.ofBitVec (productHigh s.regs.rax.toBitVec s.regs.rcx.toBitVec)}
    status := flags}

/-- The first half of the unroll uses the original full-width MUL. -/
theorem first_product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (loopProductState s flags, base + 485)) :
    Eventually (step e) P (s, base + 482) := by
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  natmulword_step 3:29 using hc
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals simpa [loopProductState, productHigh] using next _

/-- The second MUL has its own continuation, after the first store and fetch. -/
theorem second_product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (loopProductState s flags, base + 438)) :
    Eventually (step e) P (s, base + 435) := by
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  natmulword_step 3:15 using hc
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals simpa [loopProductState, productHigh] using next _

def firstCarriedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.r10.toBitVec)
      r11 := UInt64.ofBitVec (s.regs.rdx.toBitVec + BitVec.ofNat 64
        (Udivti3.addFlags s.regs.rax.toBitVec s.regs.r10.toBitVec).cf.toNat)}
    status := flags}

def secondCarriedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.r11.toBitVec)
      r10 := UInt64.ofBitVec (s.regs.rdx.toBitVec + BitVec.ofNat 64
        (Udivti3.addFlags s.regs.rax.toBitVec s.regs.r11.toBitVec).cf.toNat)}
    status := flags}

theorem first_carry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (firstCarriedState s flags, base + 495)) :
    Eventually (step e) P (s, base + 485) := by
  natmulword_step 3:30 using hc
  natmulword_step 3:31 using hc
  natmulword_step 4:0 using hc
  word_simpa [firstCarriedState] using next _

theorem second_carry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (secondCarriedState s flags, base + 448)) :
    Eventually (step e) P (s, base + 438) := by
  natmulword_step 3:16 using hc
  natmulword_step 3:17 using hc
  natmulword_step 3:18 using hc
  word_simpa [secondCarriedState] using next _

def firstStoredState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with r13 := UInt64.ofBitVec (s.regs.r8.toBitVec + 1)}
    dmem := Mem.storeInt s.dmem
      (s.regs.rbp.toBitVec + s.regs.r8.toBitVec * 8#64 - 8#64) 8 s.regs.rax.toBitVec.toInt}

def secondStoredState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (s.regs.r13.toBitVec + 1)}
    dmem := Mem.storeInt s.dmem
      (s.regs.rbp.toBitVec + s.regs.r8.toBitVec * 8#64) 8 s.regs.rax.toBitVec.toInt}

theorem first_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem
      (s.regs.rbp.toBitVec + s.regs.r8.toBitVec * 8#64 - 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (firstStoredState s, base + 504)) :
    Eventually (step e) P (s, base + 495) := by
  natmulword_step 4:1 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  have address : s.regs.rbp.toBitVec + s.regs.r8.toBitVec * BitVec.ofInt 64 8 + BitVec.ofInt 64 (-8) =
      s.regs.rbp.toBitVec + s.regs.r8.toBitVec * 8#64 - 8#64 := by
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-8) = 18446744073709551608#64 by decide]
    bv_omega
  rw [address]
  apply Delimited.store_cps
  · exact hm
  simp only [Effects.All]
  natmulword_step 4:2 using hc
  simpa [firstStoredState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next

theorem second_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem
      (s.regs.rbp.toBitVec + s.regs.r8.toBitVec * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (secondStoredState s, base + 457)) :
    Eventually (step e) P (s, base + 448) := by
  natmulword_step 3:19 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simp only [Effects.All]
  natmulword_step 3:20 using hc
  simpa [secondStoredState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next

end SszX86.NatMulWord
