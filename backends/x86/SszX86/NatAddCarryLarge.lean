import SszX86.NatAddCarryEntry
import SszX86.NatAddCarryPost

namespace SszX86.NatAdd.Carry
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem pointer_small (m : DataMem) (operand : NatOperand)
    (owned : operand.At (widthLoad m)) :
    operand.pointer = 0 ↔ isSmall operand = true := by
  cases operand with
  | small limb => simp [NatOperand.pointer, isSmall]
  | large pointer words =>
    have positive := owned.1
    have nonzero : pointer ≠ 0 := by intro h; simp [h] at positive
    simp [NatOperand.pointer, isSmall, nonzero]

theorem low_operand (m : DataMem) (operand : NatOperand)
    (owned : operand.At (widthLoad m)) :
    if isSmall operand then limbAt operand.words 0 = operand.payload else
      if operand.payload = 0 then limbAt operand.words 0 = 0 else
      Mem.loadInt m operand.pointer 8 = some ((limbAt operand.words 0).toNat : Int) := by
  cases operand with
  | small limb => simp [isSmall, NatOperand.words, NatOperand.payload, limbAt]
  | large pointer words =>
    obtain ⟨positive, aligned, room, stored⟩ := owned
    have lengthBound : words.length < 2^64 := by omega
    have empty : BitVec.ofNat 64 words.length = 0#64 ↔ words.length = 0 := by bv_omega
    simp only [isSmall, Bool.false_eq_true, if_false, NatOperand.words,
      NatOperand.payload, NatOperand.pointer, empty]
    by_cases zero : words.length = 0
    · have nil := List.eq_nil_of_length_eq_zero zero
      simp [zero, nil, limbAt]
    · simp only [zero, if_false]
      have load := widthLoad_eq m _ _ _ (stored ⟨0, by omega⟩)
      simpa [width_address, limbAt, List.getElem?_eq_getElem (show 0 < words.length by omega)] using load

/-- Complete allocation-success limb phase for every Large-left representation,
including a Small RHS and arbitrary redundant physical high zeros. -/
theorem large_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer dst : BitVec 64) (words : List (BitVec 64))
    (right : NatOperand)
    (leftOwned : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (rightOwned : right.At (widthLoad s.dmem))
    (nonzero : (NatOperand.large pointer words).wordCount ≠ 0)
    (wide : 2 ≤ SszNative.NatAdd.count (.large pointer words) right)
    (mapped : Large.Mapped s.dmem dst (8*(SszNative.NatAdd.count (.large pointer words) right+1)))
    (leftApart : Apart (.large pointer words) dst
      (8*(SszNative.NatAdd.count (.large pointer words) right+1)))
    (rightApart : Apart right dst (8*(SszNative.NatAdd.count (.large pointer words) right+1)))
    (bound : dst.toNat + 8*(SszNative.NatAdd.count (.large pointer words) right+1) ≤ 2^64)
    (rsi : get s .rsi = pointer) (rdx : get s .rdx = BitVec.ofNat 64 words.length)
    (rcx : get s .rcx = right.pointer) (r8 : get s .r8 = right.payload)
    (rax : get s .rax = BitVec.ofNat 64 (SszNative.NatAdd.count (.large pointer words) right))
    (r10 : get s .r10 = dst)
    (P : MachineState → Prop)
    (hp : ∀ t, Post s (.large pointer words) right dst t → Eventually (step e) P (t, base+1325)) :
    Eventually (step e) P (s, base+536) := by
  let count := SszNative.NatAdd.count (.large pointer words) right
  let l := limbAt words 0
  let r := limbAt right.words 0
  let next := LimbAdd.step l r 0
  have countBound : count+1 < 2^64 := by dsimp [count]; omega
  have physicalLength : words.length < 2^64 := by have := leftOwned.2.2.1; omega
  have lengthPositive : 0 < words.length := by
    have significant := Limbs.sigWords_le_length words
    change Limbs.sigWords words ≠ 0 at nonzero
    omega
  have leftPointer : get s .rsi ≠ 0 := by
    rw [rsi]
    intro zero
    have positive := leftOwned.1
    simp [zero] at positive
  have leftLength : get s .rdx ≠ 0 := by rw [rdx]; bv_omega
  have leftLoad : Mem.loadInt s.dmem (get s .rsi) 8 = some (l.toNat : Int) := by
    have load := widthLoad_eq s.dmem _ _ _ (leftOwned.2.2.2 ⟨0,lengthPositive⟩)
    simpa [rsi, width_address, l, limbAt, List.getElem?_eq_getElem lengthPositive] using load
  apply large_entry_cps e base hc s l r (isSmall right) leftPointer leftLength leftLoad
  · simpa [rcx] using pointer_small s.dmem right rightOwned
  · simpa [r8, rcx, r] using low_operand s.dmem right rightOwned
  · rw [r10]
    exact Delimited.mapped_load_zero _ _ _ 8 mapped (by omega)
  intro residual flags
  let head := {lowState s next.1 next.2 (isSmall right) flags with
    regs := {(lowState s next.1 next.2 (isSmall right) flags).regs with r15 := residual}}
  have headMemory : head.dmem = Large.fillMem s.dmem dst 0 [next.1] := by
    simp [head, lowState, Large.fillMem, r10]
  apply scalar_cps e base hc pointer dst words right count countBound leftApart rightApart P
    1 (by omega) (by dsimp [count]; omega) head next.2 (LimbAdd.step_carry_le l r 0 (by omega))
  · simpa [head, lowState, get] using rsi
  · simpa [head, lowState, get] using rdx
  · simpa [head, lowState, get] using rcx
  · simpa [head, lowState, get] using r8
  · simpa [head, lowState, get, count] using rax
  · simpa [head, lowState, get] using r10
  · simp [head, lowState, get, rax, count]
  · simp [head, lowState, get]
  · simp [head, lowState, get]
  · cases small : isSmall right <;> simp [head, lowState, get, small]
  · rw [headMemory]
    exact fill_preserves s.dmem (.large pointer words) dst 0 (8*(count+1))
      [next.1] leftOwned leftApart (by simp; omega)
  · rw [headMemory]
    exact fill_preserves s.dmem right dst 0 (8*(count+1)) [next.1]
      rightOwned rightApart (by simp; omega)
  · rw [headMemory]
    exact Large.mapped_store _ _ _ _ _ _ mapped
  intro final stable finalMemory
  apply hp final
  apply post_of_fill s final (.large pointer words) right dst leftOwned rightOwned
    leftApart rightApart bound
  · simpa only [stable.1, head, lowState] using rax
  · simpa only [stable.2.2.2.2.2.2.1, head, lowState] using r10
  · simp [stable.2.2.2.2.2.1, head, lowState, next, l, r, NatOperand.words]
  · exact stable.2.2.2.2.2.2.2.2.2.1
  · exact stable.2.2.2.2.2.2.2.2.2.2.1
  · exact stable.2.2.2.2.2.2.2.2.2.2.2
  · rw [finalMemory, headMemory, SszNative.NatAdd.writtenWords_native_loop]
    simp only [show count+1-1 = count by omega, ← fill_append]
    rw [show SszNative.NatAdd.count (.large pointer words) right + 1 = count+1 by rfl]
    rw [show words = words.drop 0 by simp,
      show right.words = right.words.drop 0 by simp, LimbAdd.loop_indexed_succ]
    simp [Large.fillMem, next, l, r, NatOperand.words, count]

end SszX86.NatAdd.Carry
