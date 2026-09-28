import SszX86.NatMulLoopFetch

namespace SszX86.NatMul.Product
open UintCodec

def guardedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := UInt64.ofBitVec (s.regs.r15.toBitVec + s.regs.rbx.toBitVec)}
    status := flags}

/-- The genuine row/column invariant discharges the first excluded panic edge. -/
theorem guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (inside : (s.regs.r15.toBitVec + s.regs.rbx.toBitVec).toNat < s.regs.r14.toBitVec.toNat)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (guardedState s flags, base + 589)) :
    Eventually (step e) P (s, base + 576) := by
  have below : ¬ s.regs.r14.toNat ≤ (s.regs.r15.toNat+s.regs.rbx.toNat)%2^64 := by
    have bound := inside
    rw [BitVec.toNat_add] at bound
    change (s.regs.r15.toNat+s.regs.rbx.toNat)%2^64 < s.regs.r14.toNat at bound
    omega
  natmul_step 5 row 2 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  natmul_step 5 row 3 using hc
  natmul_step 5 row 4 using hc
  simpa [guardedState, StatusFlags.from_result, Udivti3.cf_sub, below, Effects.All]
    using next _

def advancedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbx := UInt64.ofBitVec (s.regs.rbx.toBitVec + 1), r8 := 0}
    status := flags}

/-- The original INC, compare, and backedge finish one inner iteration. -/
theorem advance_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (advancedState s flags,
      if s.regs.rbx.toBitVec + 1 = s.regs.r13.toBitVec then base + 627 else base + 576)) :
    Eventually (step e) P (s, base + 613) := by
  have target := hc.targets ("natMul_u576", 576) (by decide)
  natmul_step 5 row 12 using hc
  natmul_step 5 row 13 using hc
  natmul_step 5 row 14 using hc
  natmul_step 5 row 15 using hc
  by_cases equal : s.regs.r13.toBitVec = s.regs.rbx.toBitVec+1#64
  all_goals simpa [advancedState, StatusFlags.from_result, Udivti3.zf_sub, target,
    Effects.All, eq_comm, equal, show (1 : BitVec 64) = 1#64 by decide] using next _

def carryGuardedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r15 := UInt64.ofBitVec (s.regs.r15.toBitVec + s.regs.r13.toBitVec)}
    status := flags}

/-- PC633 checks row+rightCount, not the last inner index. -/
theorem carry_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (inside : (s.regs.r15.toBitVec + s.regs.r13.toBitVec).toNat < s.regs.r14.toBitVec.toNat)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (carryGuardedState s flags, base + 639)) :
    Eventually (step e) P (s, base + 627) := by
  have below : ¬ s.regs.r14.toNat ≤ (s.regs.r13.toNat+s.regs.r15.toNat)%2^64 := by
    have bound := inside
    rw [BitVec.toNat_add] at bound
    change (s.regs.r15.toNat+s.regs.r13.toNat)%2^64 < s.regs.r14.toNat at bound
    simpa only [Nat.add_comm] using Nat.not_le_of_lt bound
  natmul_step 5 row 16 using hc
  natmul_step 5 row 17 using hc
  natmul_step 5 row 18 using hc
  simpa [carryGuardedState, StatusFlags.from_result, Udivti3.cf_sub,
    BitVec.add_comm, below, Effects.All] using next _

def carryStoredState (s : MachineData) (dst : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec dst}
    dmem := Mem.storeInt s.dmem (dst + s.regs.r15.toBitVec * 8#64) 8 s.regs.r9.toBitVec.toInt}

theorem carry_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (dst : BitVec 64)
    (baseLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (dst.toNat : Int))
    (hmapped : ∃ old, Mem.loadInt s.dmem (dst + s.regs.r15.toBitVec * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (carryStoredState s dst, base + 648)) :
    Eventually (step e) P (s, base + 639) := by
  natmul_step 5 row 19 using hc
  natmul_load baseLoad
  natmul_step 5 row 20 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hmapped
  simpa [Effects.All, carryStoredState] using next

def outerAdvancedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r10 := UInt64.ofBitVec (s.regs.r10.toBitVec + 8#64), r15 := s.regs.r11}
    status := flags}

theorem outer_advance_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (outerAdvancedState s flags,
      if s.regs.r11 = s.regs.r12 then base + 664 else base + 512)) :
    Eventually (step e) P (s, base + 648) := by
  have target := hc.targets ("natMul_u512", 512) (by decide)
  natmul_step 5 row 21 using hc
  natmul_step 5 row 22 using hc
  natmul_step 5 row 23 using hc
  natmul_step 5 row 24 using hc
  have addReg : (OfNat.ofNat 8 : UInt64)+s.regs.r10 = s.regs.r10+OfNat.ofNat 8 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_add]
    bv_omega
  by_cases equal : s.regs.r11 = s.regs.r12
  all_goals simpa [outerAdvancedState, StatusFlags.from_result, Udivti3.zf_sub,
    UInt64.toBitVec_inj, target, Effects.All, equal, addReg] using next _

end SszX86.NatMul.Product
