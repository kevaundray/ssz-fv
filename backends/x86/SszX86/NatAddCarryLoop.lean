import SszX86.NatAddCarryFetch

namespace SszX86.NatAdd.Carry
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Registers and SIMD storage untouched by the complete scalar limb loop. -/
def Stable (s t : MachineData) : Prop :=
  t.regs.rax = s.regs.rax ∧ t.regs.rsi = s.regs.rsi ∧
  t.regs.rdx = s.regs.rdx ∧ t.regs.rcx = s.regs.rcx ∧
  t.regs.r8 = s.regs.r8 ∧ t.regs.r9 = s.regs.r9 ∧
  t.regs.r10 = s.regs.r10 ∧ t.regs.r11 = s.regs.r11 ∧
  t.regs.rbp = s.regs.rbp ∧ t.regs.rdi = s.regs.rdi ∧
  t.regs.rsp = s.regs.rsp ∧ t.zmms = s.zmms

theorem stable_trans {a b c : MachineData} (hab : Stable a b) (hbc : Stable b c) :
    Stable a c := by
  rcases hab with ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12⟩
  rcases hbc with ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12⟩
  exact ⟨b1.trans a1,b2.trans a2,b3.trans a3,b4.trans a4,b5.trans a5,b6.trans a6,
    b7.trans a7,b8.trans a8,b9.trans a9,b10.trans a10,b11.trans a11,b12.trans a12⟩

def isSmall : NatOperand → Bool
  | .small _ => true
  | .large _ _ => false

/-- The scalar loop's branch loads exactly the original zero-extended word. -/
theorem fetch_word (m : DataMem) (operand : NatOperand) (index : Nat)
    (owned : operand.At (widthLoad m)) (hi : 0 < index) (hb : index < 2^64) :
    (if ¬isSmall operand ∧ (BitVec.ofNat 64 index).toNat < operand.payload.toNat then
      Mem.loadInt m (operand.pointer + BitVec.ofNat 64 index * 8#64) 8 =
        some ((limbAt operand.words index).toNat : Int)
      else limbAt operand.words index = 0) := by
  cases operand with
  | small limb => simp [isSmall, small_limbAt limb index hi]
  | large pointer words =>
    obtain ⟨positive, aligned, room, stored⟩ := owned
    have hlength : words.length < 2^64 := by omega
    simp only [isSmall, Bool.false_eq_true, not_false_eq_true, true_and,
      NatOperand.payload, NatOperand.pointer, NatOperand.words,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hlength]
    by_cases present : index < words.length
    · simp only [present, if_true]
      have load := widthLoad_eq m _ _ _ (stored ⟨index, present⟩)
      simpa [width_address, limbAt, List.getElem?_eq_getElem present,
        BitVec.ofNat_mul, Nat.mul_comm] using load
    · simp [present, limbAt, List.getElem?_eq_none (by omega)]

/-- Every scalar iteration, including the redundant final zero, is executed.
The induction ranges over the arbitrary remaining physical limb count. -/
theorem scalar_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (leftPointer dst : BitVec 64) (left : List (BitVec 64)) (right : NatOperand)
    (count : Nat) (hcount : count + 1 < 2^64)
    (leftApart : Apart (.large leftPointer left) dst (8*(count+1)))
    (rightApart : Apart right dst (8*(count+1)))
    (P : MachineState → Prop) :
    ∀ index, 0 < index → index ≤ count → ∀ (s : MachineData) (carry : Nat),
    carry ≤ 1 →
    get s .rsi = leftPointer → get s .rdx = BitVec.ofNat 64 left.length →
    get s .rcx = right.pointer → get s .r8 = right.payload →
    get s .rax = BitVec.ofNat 64 count → get s .r10 = dst →
    get s .r11 = -BitVec.ofNat 64 count → get s .rbx = BitVec.ofNat 64 index →
    get s .r14 = BitVec.ofNat 64 carry →
    (get s .rbp).extractLsb' 0 8 = (if isSmall right then 1#8 else 0#8) →
    (NatOperand.large leftPointer left).At (widthLoad s.dmem) →
    right.At (widthLoad s.dmem) → Large.Mapped s.dmem dst (8*(count+1)) →
    (∀ t, Stable s t →
      t.dmem = Large.fillMem s.dmem dst index
        (LimbAdd.loop (count+1-index) (left.drop index) (right.words.drop index) carry).1 →
      Eventually (step e) P (t, base + 1325)) →
    Eventually (step e) P (s, base + 1008) := by
  intro index
  induction remaining : count + 1 - index using Nat.strongRecOn generalizing index with
  | ind remaining ih =>
    intro positive within s carry carryBound rsi rdx rcx r8 rax r10 r11 rbx r14 bpl
      leftOwned rightOwned mapped hp
    let l := limbAt left index
    let r := limbAt right.words index
    let next := LimbAdd.step l r carry
    have indexBound : index < 2^64 := by omega
    have leftLoad := fetch_word s.dmem (.large leftPointer left) index leftOwned positive indexBound
    have rightLoad := fetch_word s.dmem right index rightOwned positive indexBound
    apply fetch_cps e base hc s l r (isSmall right) bpl
    · simpa [get, rbx, rdx, rsi, isSmall, NatOperand.payload, NatOperand.pointer,
        NatOperand.words, l] using leftLoad
    · simpa [get, rbx, r8, rcx, r] using rightLoad
    intro loadFlags
    let loaded := fetchState s l r loadFlags
    apply body_cps e base hc loaded
    · have hm := Large.mapped_load s.dmem dst (8*(count+1)) (8*index) 8 mapped (by omega)
      simpa [loaded, fetchState, get, r10, rbx, BitVec.ofNat_mul, Nat.mul_comm] using hm
    intro addFlags flags
    let t := advanced (stored (addState loaded addFlags)) flags
    have arithmetic := two_adds l r carry carryBound
    have memory : t.dmem = Mem.storeInt s.dmem (dst + BitVec.ofNat 64 (8*index)) 8 next.1.toInt := by
      simp only [t, advanced, stored, addState, loaded, fetchState, get,
        Reg64s.get64, added, r10, rbx, r14] at *
      rw [arithmetic.1]
      simp [next, BitVec.ofNat_mul, Nat.mul_comm]
    have stable : Stable s t := by simp [Stable, t, advanced, stored, addState, loaded, fetchState]
    have nextIndex : get t .rbx = BitVec.ofNat 64 (index+1) := by
      simp [t, advanced, stored, addState, loaded, fetchState, get, rbx, BitVec.ofNat_add]
    have nextCarry : get t .r14 = BitVec.ofNat 64 next.2 := by
      simpa [t, advanced, stored, addState, loaded, fetchState, get, carried, r14,
        next] using arithmetic.2
    have terminate : get loaded .r11 + get loaded .rbx + 1#64 = 1#64 ↔ index = count := by
      simp only [loaded, fetchState, get, Reg64s.get64, r11, rbx]
      bv_omega
    have recurrence :
        (LimbAdd.loop (count+1-index) (left.drop index) (right.words.drop index) carry).1 =
          next.1 :: (LimbAdd.loop (count-index) (left.drop (index+1))
            (right.words.drop (index+1)) next.2).1 := by
      rw [show count+1-index = (count-index)+1 by omega,
        LimbAdd.loop_indexed_succ]
      rfl
    by_cases last : index = count
    · simp only [terminate.mpr last, if_true]
      apply hp t stable
      rw [recurrence, show count-index = 0 by omega]
      simpa [LimbAdd.loop, Large.fillMem] using memory
    · simp only [show ¬ get loaded .r11 + get loaded .rbx + 1#64 = 1#64
        from fun h => last (terminate.mp h), if_false]
      apply ih (count+1-(index+1)) (by omega) (index+1) rfl (by omega) (by omega) t next.2
        (LimbAdd.step_carry_le l r carry carryBound)
      · simpa only [get, Reg64s.get64, stable.2.1] using rsi
      · simpa only [get, Reg64s.get64, stable.2.2.1] using rdx
      · simpa only [get, Reg64s.get64, stable.2.2.2.1] using rcx
      · simpa only [get, Reg64s.get64, stable.2.2.2.2.1] using r8
      · simpa only [get, Reg64s.get64, stable.1] using rax
      · simpa only [get, Reg64s.get64, stable.2.2.2.2.2.2.1] using r10
      · simpa only [get, Reg64s.get64, stable.2.2.2.2.2.2.2.1] using r11
      · exact nextIndex
      · exact nextCarry
      · simpa [get, stable.2.2.2.2.2.2.2.2.1] using bpl
      · rw [memory]
        exact fill_preserves s.dmem (.large leftPointer left) dst index (8*(count+1))
          [next.1] leftOwned leftApart (by simp; omega)
      · rw [memory]
        exact fill_preserves s.dmem right dst index (8*(count+1)) [next.1]
          rightOwned rightApart (by simp; omega)
      · rw [memory]
        exact Large.mapped_store _ _ _ _ _ _ mapped
      intro final preserved finalMemory
      apply hp final (stable_trans stable preserved)
      rw [recurrence, Large.fillMem, finalMemory, memory]
      congr 2
      omega

end SszX86.NatAdd.Carry
