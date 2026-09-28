import SszX86.NatMulWordCore

namespace SszX86.NatMulWord.Tail
open UintCodec

def indexState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r8 := UInt64.ofBitVec (s.regs.r8.toBitVec+2#64)}, status := flags}

def pointerState (s : MachineData) (start : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r14 := UInt64.ofBitVec (s.regs.r14.toBitVec+start)}, status := flags}

def zeroState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 0}, status := flags}

def address (s : MachineData) : BitVec 64 := s.regs.r14.toBitVec+s.regs.r8.toBitVec*8#64

def storedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := s.regs.r10}
    dmem := Mem.storeInt s.dmem (address s) 8 s.regs.r10.toBitVec.toInt
    status := flags}

def even (s : MachineData) : Prop := s.regs.r15.toBitVec.extractLsb' 0 8 &&& 1#8 = 0#8

instance (s : MachineData) : Decidable (even s) := by
  unfold even
  infer_instance

theorem index_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (indexState s flags, base+706)) :
    Eventually (step e) P (s, base+702) := by
  natmulword_step 5:22 using hc
  simpa [indexState, UInt64.add_comm] using next _

theorem pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (start : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.rsp.toBitVec+8#64) 8 = some (start.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (pointerState s start flags, base+711)) :
    Eventually (step e) P (s, base+706) := by
  natmulword_step 5:23 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  natmulword_load loaded
  simpa [pointerState, BitVec.add_comm] using next _

theorem parity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if even s then base+741 else base+717)) :
    Eventually (step e) P (s, base+711) := by
  have target := hc.targets ("natMulWord_u741", 741) (by decide)
  natmulword_step 5:24 using hc
  constructor <;> natmulword_step 5:25 using hc
  all_goals by_cases parity : 1#8 &&& s.regs.r15.toBitVec.setWidth 8 = 0#8
  all_goals simpa [even, StatusFlags.from_result, parity, target, Effects.All, BitVec.and_comm] using next _

theorem fetch_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (loaded : s.regs.r8.toNat < s.regs.r9.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec+s.regs.r8.toBitVec*8#64) 8 = some 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (zeroState s flags, base+730)) :
    Eventually (step e) P (s, base+717) := by
  have target := hc.targets ("natMulWord_u728", 728) (by decide)
  natmulword_step 5:26 using hc
  natmulword_step 5:27 using hc
  by_cases inside : s.regs.r8.toNat < s.regs.r9.toNat
  · simp [StatusFlags.from_result, inside, Effects.All]
    natmulword_step 5:28 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    have zeroLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec+s.regs.r8.toBitVec*8#64) 8 =
        some ((0#64).toNat : Int) := loaded inside
    natmulword_load zeroLoad
    natmulword_step 5:29 using hc
    simpa [zeroState] using next _
  · simp [StatusFlags.from_result, inside, target, Effects.All]
    natmulword_step 5:30 using hc
    constructor <;> simpa [zeroState] using next _

theorem multiply_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.rax.toBitVec = 0#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (zeroState s flags, base+734)) :
    Eventually (step e) P (s, base+730) := by
  have zeroReg : s.regs.rax = 0 := UInt64.toBitVec_inj.mp zero
  natmulword_step 5:31 using hc
  constructor <;> constructor <;> constructor <;> constructor
  all_goals simpa [zero, zeroReg, zeroState] using next _

theorem store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.rax.toBitVec = 0#64)
    (hm : Large.Mapped s.dmem (address s) 8) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (storedState s flags, base+741)) :
    Eventually (step e) P (s, base+734) := by
  have zeroReg : s.regs.rax = 0 := UInt64.toBitVec_inj.mp zero
  natmulword_step 6:0 using hc
  natmulword_step 6:1 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 8) (byteCount := 8)
    · exact hm
    · decide
  simpa [storedState, address, zero, zeroReg, Effects.All] using next _

/-- The even path does not demand mapping for an out-of-allocation extra limb.
Only an odd count fetches the checked zero-extended input and stores its carry. -/
theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (loaded : ¬ even s → s.regs.r8.toNat < s.regs.r9.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec+s.regs.r8.toBitVec*8#64) 8 = some 0)
    (hm : ¬ even s → Large.Mapped s.dmem (address s) 8)
    (P : MachineState → Prop)
    (nextEven : even s → ∀ flags, Eventually (step e) P ({s with status := flags}, base+741))
    (nextOdd : ¬ even s → ∀ flags, Eventually (step e) P (storedState s flags, base+741)) :
    Eventually (step e) P (s, base+711) := by
  apply parity_cps e base hc s P
  intro flags
  by_cases parity : even s
  · simpa only [parity, ↓reduceIte] using nextEven parity flags
  · simp only [parity, ↓reduceIte]
    apply fetch_zero_cps e base hc
    · exact loaded parity
    intro fetchFlags
    apply multiply_zero_cps e base hc _ rfl
    intro mulFlags
    apply store_cps e base hc _ rfl
    · exact hm parity
    intro storeFlags
    simpa only [storedState, zeroState] using nextOdd parity storeFlags

end SszX86.NatMulWord.Tail
