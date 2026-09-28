import SszX86.NatMulProductBounds
import SszX86.Udivti3Math

namespace SszX86.NatMul.Product
open UintCodec

/-- PC493 restores the right pointer and records the allocated base. -/
def setupState (s : MachineData) (right : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsi := UInt64.ofBitVec right, r10 := s.regs.rbx}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 s.regs.rbx.toBitVec.toInt}

theorem setup_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (right : BitVec 64)
    (rightLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (right.toNat : Int))
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (setupState s right, base + 512)) :
    Eventually (step e) P (s, base + 493) := by
  natmul_step 4 row 13 using hc
  natmul_load rightLoad
  natmul_step 4 row 14 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt, Width.bytes,
      show BitVec.ofInt 64 8 = 8#64 by decide] using slot
  simp only [Effects.All]
  natmul_step 4 row 15 using hc
  natmul_step 4 row 16 using hc
  simpa [setupState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next

def fetchedState (s : MachineData) (pointer factor : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec pointer, rcx := UInt64.ofBitVec factor}
    status := flags}

/-- In the allocating branch the original significant index is a physical limb.
The pointer and length tests are executed, not replaced by a synthetic fetch. -/
theorem fetch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload factor : BitVec 64)
    (nonzero : pointer ≠ 0#64)
    (inside : s.regs.r15.toBitVec.toNat < payload.toNat)
    (pointerLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 =
      some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
      some (payload.toNat : Int))
    (wordLoad : Mem.loadInt s.dmem
      (pointer + s.regs.r15.toBitVec * 8#64) 8 = some (factor.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (fetchedState s pointer factor flags, base + 554)) :
    Eventually (step e) P (s, base + 512) := by
  natmul_step 4 row 17 using hc
  natmul_load pointerLoad
  natmul_step 4 row 18 using hc
  simp [StatusFlags.from_result, nonzero, Effects.All]
  natmul_step 4 row 19 using hc
  natmul_load payloadLoad
  natmul_step 4 row 20 using hc
  have below : ¬ payload.toNat ≤ s.regs.r15.toNat := by
    change s.regs.r15.toNat < payload.toNat at inside
    omega
  simp [StatusFlags.from_result, below, Effects.All]
  natmul_step 4 row 21 using hc
  natmul_load pointerLoad
  natmul_step 4 row 22 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natmul_load wordLoad
  natmul_step 4 row 23 using hc
  simpa [fetchedState] using next _

def initializedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r11 := UInt64.ofBitVec (s.regs.r15.toBitVec + 1#64)
      rbx := 0
      r9 := 0
      r8 := 0}
    status := flags}

theorem initialize_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (initializedState s flags, base + 576)) :
    Eventually (step e) P (s, base + 554) := by
  natmul_step 4 row 29 using hc
  natmul_step 4 row 30 using hc
  constructor <;> natmul_step 4 row 31 using hc
  all_goals constructor <;> natmul_step 5 row 0 using hc
  all_goals constructor <;> natmul_step 5 row 1 using hc
  all_goals simpa [initializedState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next _

end SszX86.NatMul.Product
