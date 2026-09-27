import SszX86.NatDivisionCall
import SszX86.NatDivisionMath

namespace SszX86.NatDivision.Loop

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def get (s : MachineData) (r : Reg64) : BitVec 64 := s.regs.get64 r

def arguments (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r12 := UInt64.ofBitVec limb
      rdi := UInt64.ofBitVec limb
      rsi := s.regs.r15
      rdx := s.regs.rbx
      rcx := 0}
    status := flags}

/-- The load and actual SysV argument moves before the linked wide divider. -/
theorem arguments_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : Mem.loadInt s.dmem (get s .r14 + get s .rbp) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (arguments s limb flags, base + 783)) :
    Eventually (step e) P (s, base + 768) := by
  have hl : Mem.loadInt s.dmem (s.regs.r14.toBitVec + s.regs.rbp.toBitVec) 8 =
      some (limb.toNat : Int) := loaded
  natdiv_step 207 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  natdiv_load hl
  natdiv_step 208 using hc
  natdiv_step 209 using hc
  natdiv_step 210 using hc
  natdiv_step 211 using hc
  constructor <;> simpa [arguments, get, Reg64s.get64] using next _

def productHigh (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.unsigned * b.unsigned) >>> 64)

def tailState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (get s .rax * get s .rbx)
      rdx := UInt64.ofBitVec (productHigh (get s .rax) (get s .rbx))
      r15 := UInt64.ofBitVec (get s .r12 - get s .rax * get s .rbx)}
    dmem := Mem.storeInt s.dmem (get s .r14 + get s .rbp) 8 (get s .rax).toInt
    status := flags}

def productState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (get s .rax * get s .rbx)
      rdx := UInt64.ofBitVec (productHigh (get s .rax) (get s .rbx))}
    status := flags}

def remainderState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r15 := UInt64.ofBitVec (get s .r12 - get s .rax)}
    status := flags}

private theorem product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (productState s flags, base + 796)) :
    Eventually (step e) P (s, base + 793) := by
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  natdiv_step 214 using hc
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals simpa [productState, productHigh, get, Reg64s.get64] using next _

private theorem remainder_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (remainderState s flags, base + 802)) :
    Eventually (step e) P (s, base + 796) := by
  natdiv_step 215 using hc
  natdiv_step 216 using hc
  simpa [remainderState, get, Reg64s.get64] using next _

/-- The quotient store and real MUL/SUB recover the low-word remainder. -/
theorem tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r14 + get s .rbp) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (tailState s flags, base + 802)) :
    Eventually (step e) P (s, base + 789) := by
  natdiv_step 213 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simp only [Effects.All]
  apply product_cps e base hc
  intro productFlags
  apply remainder_cps e base hc
  intro finalFlags
  simpa [tailState, productState, remainderState, get, Reg64s.get64] using next finalFlags

def advance (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbp := UInt64.ofBitVec (get s .rbp - 8#64)}
    status := flags}

/-- The unsigned physical index controls the back edge; no signed-capacity
restriction is imposed on the allocation. -/
theorem advance_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (advance s flags, if get s .rbp = 0 then base + 477 else base + 768)) :
    Eventually (step e) P (s, base + 802) := by
  have target := hc.targets ("natDivision_u768", 768) (by decide)
  have decrement : UInt64.ofBitVec (get s .rbp - 8#64) =
      (18446744073709551608 : UInt64) + s.regs.rbp := by
    apply UInt64.eq_of_toBitVec_eq
    change s.regs.rbp.toBitVec - 8#64 = 18446744073709551608#64 + s.regs.rbp.toBitVec
    rw [BitVec.sub_eq_add_neg]
    exact BitVec.add_comm _ _
  change ∀ flags, Eventually (step e) P
    (advance s flags, if s.regs.rbp.toBitVec = 0#64 then base + 477 else base + 768) at next
  natdiv_step 217 using hc
  natdiv_step 218 using hc
  natdiv_step 219 using hc
  by_cases zero : s.regs.rbp.toBitVec = 0#64
  · simp [StatusFlags.from_result, zero, Effects.All]
    natdiv_step 220 using hc
    have continuation := next
    simp only [zero, ↓reduceIte] at continuation
    simpa only [advance, decrement] using continuation _
  · simp [StatusFlags.from_result, zero, target, Effects.All]
    have continuation := next
    simp only [zero, ↓reduceIte] at continuation
    simpa only [advance, decrement] using continuation _

end SszX86.NatDivision.Loop
