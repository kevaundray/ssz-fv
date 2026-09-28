import SszX86.NatAddCarryPair
import SszX86.NatAddCarryPairMath
import SszX86.NatAddCarryLoop

namespace SszX86.NatAdd.Carry.Pair
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def Stable (s t : MachineData) : Prop :=
  t.regs.rax = s.regs.rax ∧ t.regs.rcx = s.regs.rcx ∧
  t.regs.r8 = s.regs.r8 ∧ t.regs.r9 = s.regs.r9 ∧
  t.regs.r10 = s.regs.r10 ∧ t.regs.r11 = s.regs.r11 ∧
  t.regs.rbx = s.regs.rbx ∧ t.regs.rdi = s.regs.rdi ∧
  t.regs.rsp = s.regs.rsp ∧ t.zmms = s.zmms

theorem stable_trans {a b c : MachineData} (hab : Stable a b) (hbc : Stable b c) :
    Stable a c := by
  rcases hab with ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩
  rcases hbc with ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10⟩
  exact ⟨b1.trans a1,b2.trans a2,b3.trans a3,b4.trans a4,b5.trans a5,
    b6.trans a6,b7.trans a7,b8.trans a8,b9.trans a9,b10.trans a10⟩

/-- Induction is over the arbitrary number of real two-limb machine iterations. -/
theorem loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (pointer dst : BitVec 64) (right : List (BitVec 64)) (capacity : Nat)
    (apart : Carry.Apart (.large pointer right) dst (8*capacity))
    (physical : capacity < 2^64) (P : MachineState → Prop) :
    ∀ pairs, 0 < pairs → ∀ index, 0 < index → index + 2*pairs ≤ capacity →
    ∀ (s : MachineData) (carry : Nat), carry ≤ 1 →
    get s .rcx = pointer → get s .r8 = BitVec.ofNat 64 right.length →
    get s .rbx = dst + 8#64 → get s .rsi = BitVec.ofNat 64 index →
    get s .r11 = BitVec.ofNat 64 (index+2*pairs-1) →
    get s .r14 = BitVec.ofNat 64 carry →
    (NatOperand.large pointer right).At (widthLoad s.dmem) →
    Large.Mapped s.dmem dst (8*capacity) →
    (∀ t, Stable s t →
      get t .rdx = BitVec.ofNat 64 (index+2*pairs-2) →
      get t .r14 = BitVec.ofNat 64 (LimbAdd.loop (2*pairs) [] (right.drop index) carry).2 →
      t.dmem = Large.fillMem s.dmem dst index
        (LimbAdd.loop (2*pairs) [] (right.drop index) carry).1 →
      Eventually (step e) P (t, base+1297)) →
    Eventually (step e) P (s, base+1252) := by
  intro pairs
  induction pairs with
  | zero => intro positive; omega
  | succ pairs ih =>
    intro positive index indexPositive within s carry carryBound rcx r8 rbx rsi r11 r14
      owned hmapped hp
    let first := limbAt right index
    let second := limbAt right (index+1)
    let one := LimbAdd.step 0 first carry
    let two := LimbAdd.step 0 second one.2
    have firstArithmetic := one_add first carry carryBound
    have secondArithmetic := one_add second one.2 (LimbAdd.step_carry_le 0 first carry carryBound)
    have firstEq : firstWord s first = one.1 := by
      simpa [firstWord, get, r14, one] using firstArithmetic.1
    have carryEq : (firstCarry s first).toNat = one.2 := by
      simpa [firstCarry, get, r14, one] using firstArithmetic.2
    have secondEq : secondWord s first second = two.1 := by
      simpa [secondWord, carryEq, two] using secondArithmetic.1
    have secondCarryEq : (secondCarry s first second).toNat = two.2 := by
      simpa [secondCarry, carryEq, two] using secondArithmetic.2
    have addr1 : firstAddress s = dst + BitVec.ofNat 64 (8*index) := by
      simp only [firstAddress, get, rbx, rsi]
      bv_omega
    have addr2 : secondAddress s = dst + BitVec.ofNat 64 (8*(index+1)) := by
      simp only [secondAddress, get, rbx, rsi]
      bv_omega
    let m := Mem.storeInt s.dmem (dst + BitVec.ofNat 64 (8*index)) 8 one.1.toInt
    have owned' : (NatOperand.large pointer right).At (widthLoad m) :=
      fill_preserves s.dmem (.large pointer right) dst index (8*capacity) [one.1]
        owned apart (by simp; omega)
    have hmapped' : Large.Mapped m dst (8*capacity) := Large.mapped_store _ _ _ _ _ _ hmapped
    apply pair_cps e base hc s first second
    · have h := fetch_word s.dmem (.large pointer right) index owned indexPositive (by omega)
      simpa [get, rsi, r8, rcx, isSmall, NatOperand.words,
        NatOperand.pointer, NatOperand.payload, first] using h
    · have h := fetch_word m (.large pointer right) (index+1) owned' (by omega) (by omega)
      simpa [get, rsi, r8, rcx, isSmall, NatOperand.words,
        NatOperand.pointer, NatOperand.payload, second, BitVec.ofNat_add,
        BitVec.ofNat_mul, BitVec.mul_add, BitVec.add_mul, BitVec.add_assoc,
        addr1, firstEq, m, Nat.mul_comm] using h
    · rw [addr1]
      exact Large.mapped_load _ _ _ (8*index) 8 hmapped (by omega)
    · rw [addr1, firstEq, addr2]
      exact Large.mapped_load _ _ _ (8*(index+1)) 8 hmapped' (by omega)
    intro flags
    let t := pairState s first second flags
    have stable : Stable s t := by simp [Stable, t, pairState]
    have tMemory : t.dmem = Large.fillMem s.dmem dst index [one.1,two.1] := by
      simp [t, pairState, memory, addr1, addr2, firstEq, secondEq, Large.fillMem]
    have indexReg : s.regs.rsi.toBitVec = BitVec.ofNat 64 index := by
      simpa only [get, Reg64s.get64] using rsi
    have tCarry : get t .r14 = BitVec.ofNat 64 two.2 := by
      simp [t, pairState, get, Reg64s.get64, secondCarryEq]
    have tIndex : get t .rsi = BitVec.ofNat 64 (index+2) := by
      simp [t, pairState, get, Reg64s.get64, indexReg, BitVec.ofNat_add]
    have tLast : get t .rdx = BitVec.ofNat 64 index := by
      simp [t, pairState, get, Reg64s.get64, indexReg]
    have recurrence :
        LimbAdd.loop (2*(pairs+1)) [] (right.drop index) carry =
          let rest := LimbAdd.loop (2*pairs) [] (right.drop (index+2)) two.2
          (one.1 :: two.1 :: rest.1, rest.2) := by
      have firstStep := LimbAdd.loop_indexed_succ (2*pairs+1) index
        ([] : List (BitVec 64)) right carry
      have secondStep := LimbAdd.loop_indexed_succ (2*pairs) (index+1)
        ([] : List (BitVec 64)) right one.2
      simp only [List.drop_nil, List.getElem?_nil, Option.getD_none] at firstStep secondStep
      rw [show 2*(pairs+1) = (2*pairs+1)+1 by omega, firstStep, secondStep]
    by_cases last : pairs = 0
    · subst pairs
      have done : get s .rsi + 1#64 = get s .r11 := by
        simp only [rsi, r11]
        bv_omega
      simp only [done, ite_true]
      apply hp t stable
      · simpa using tLast
      · rw [recurrence]
        exact tCarry
      · rw [recurrence]
        exact tMemory
    · have again : get s .rsi + 1#64 ≠ get s .r11 := by
        simp only [rsi, r11]
        bv_omega
      simp only [again, ite_false]
      apply ih (by omega) (index+2) (by omega) (by omega) t two.2
        (LimbAdd.step_carry_le 0 second one.2 (LimbAdd.step_carry_le 0 first carry carryBound))
      · simpa only [get, Reg64s.get64, stable.2.1] using rcx
      · simpa only [get, Reg64s.get64, stable.2.2.1] using r8
      · simpa only [get, Reg64s.get64, stable.2.2.2.2.2.2.1] using rbx
      · exact tIndex
      · simpa only [get, Reg64s.get64, stable.2.2.2.2.2.1,
          show index+2+2*pairs-1 = index+2*(pairs+1)-1 by omega] using r11
      · exact tCarry
      · rw [tMemory]
        exact fill_preserves _ _ _ _ (8*capacity) _ owned apart (by simp; omega)
      · rw [tMemory]
        exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ hmapped)
      intro final finalStable finalIndex finalCarry finalMemory
      apply hp final (stable_trans stable finalStable)
      · simpa [show index+2+2*pairs-2 = index+2*(pairs+1)-2 by omega] using finalIndex
      · simpa [recurrence] using finalCarry
      · rw [recurrence, finalMemory, tMemory]
        exact (fill_append s.dmem dst index [one.1, two.1]
          (LimbAdd.loop (2*pairs) [] (right.drop (index+2)) two.2).1).symm

end SszX86.NatAdd.Carry.Pair
