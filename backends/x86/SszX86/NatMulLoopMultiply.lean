import SszX86.NatMulLoopControl
import SszX86.WordNormalize

namespace SszX86.NatMul.Product
open UintCodec

/-- This is precisely the high-half expression in Kraken's MUL semantics. -/
def rawHigh (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.unsigned * b.unsigned) >>> 64)

def multipliedState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rcx.toBitVec * limb)
      rdx := UInt64.ofBitVec (rawHigh s.regs.rcx.toBitVec limb)}
    status := flags}

/-- All four undefined MUL flags are quantified; the following ADD overwrites them. -/
theorem multiply_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rbx.toBitVec * 8#64) 8 =
      some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (multipliedState s limb flags, base + 596)) :
    Eventually (step e) P (s, base + 589) := by
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  natmul_step 5 row 5 using hc
  natmul_step 5 row 6 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natmul_load loaded
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals simpa [multipliedState, rawHigh] using next _

def carriedLow (s : MachineData) : BitVec 64 := s.regs.r9.toBitVec + s.regs.rax.toBitVec

def carriedHigh (s : MachineData) : BitVec 64 :=
  s.regs.rdx.toBitVec + BitVec.ofNat 64
    (Udivti3.addFlags s.regs.r9.toBitVec s.regs.rax.toBitVec).cf.toNat

def carriedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (carriedLow s), r9 := UInt64.ofBitVec (carriedHigh s)}
    status := flags}

/-- ADD/ADC consumes the previous inner carry, with the real zero high carry. -/
theorem add_carry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zeroHigh : s.regs.r8 = 0) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (carriedState s flags, base + 605)) :
    Eventually (step e) P (s, base + 596) := by
  natmul_step 5 row 7 using hc
  natmul_step 5 row 8 using hc
  natmul_step 5 row 9 using hc
  word_simpa [carriedState, carriedLow, carriedHigh, zeroHigh] using next _

def updatedWord (s : MachineData) (old : BitVec 64) : BitVec 64 := s.regs.rax.toBitVec + old

def updatedCarry (s : MachineData) (old : BitVec 64) : BitVec 64 :=
  s.regs.r9.toBitVec + BitVec.ofNat 64 (Udivti3.addFlags s.regs.rax.toBitVec old).cf.toNat

def updatedState (s : MachineData) (old : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r9 := UInt64.ofBitVec (updatedCarry s old)}
    dmem := Mem.storeInt s.dmem (s.regs.r10.toBitVec + s.regs.rbx.toBitVec * 8#64)
      8 (updatedWord s old).toInt
    status := flags}

/-- The destination ADD is a genuine load/modify/store, followed by its ADC. -/
theorem update_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.r10.toBitVec + s.regs.rbx.toBitVec * 8#64) 8 =
      some (old.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (updatedState s old flags, base + 613)) :
    Eventually (step e) P (s, base + 605) := by
  natmul_step 5 row 10 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natmul_load loaded
  apply Delimited.store_cps
  · exact ⟨_, loaded⟩
  simp only [Effects.All]
  natmul_step 5 row 11 using hc
  word_simpa [updatedState, updatedWord, updatedCarry] using next _

end SszX86.NatMul.Product
