import SszX86.NatAddLowWords
import SszX86.NatAddSmallPhase

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure LeftLow (s t : MachineData) (operand : NatOperand) : Prop where
  frame : ControlFrame s t
  low : t.regs.rdx.toBitVec = SszNative.NatAdd.lowWord operand
  pointer : t.regs.rcx = s.regs.rcx
  payload : t.regs.r8 = s.regs.r8
  marker : t.regs.r10 = s.regs.r10

/-- A nonzero significant count makes the empty-Large low-word branch
unreachable; it does not require the original list to be normalized. -/
theorem left_low_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.rdx.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (nonzero : operand.wordCount ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ t, LeftLow s t operand → Eventually (step e) P (t, base + 226)) :
    Eventually (step e) P (s, base + 209) := by
  cases operand with
  | small limb =>
    apply left_low_dispatch e base hc s P
    · intro hp flags
      apply next
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, rfl, rfl⟩
      simpa only [SszNative.NatAdd.lowWord, NatOperand.words,
        List.getElem?_cons_zero, Option.getD_some, NatOperand.payload] using payload
    · intro hp
      exact False.elim (hp pointer)
    · intro hp
      exact False.elim (hp pointer)
  | large p words =>
    have positive := stored.1
    have extent := stored.2.2.1
    have count := Limbs.sigWords_le_length words
    have nonempty : 0 < words.length := by
      change Limbs.sigWords words ≠ 0 at nonzero
      omega
    have pNonzero : p ≠ 0#64 := by intro hz; simp [hz] at positive
    have lengthNonzero : s.regs.rdx.toBitVec ≠ 0#64 := by
      rw [payload]
      change BitVec.ofNat 64 words.length ≠ 0#64
      bv_omega
    apply left_low_dispatch e base hc s P
    · intro hp
      exact False.elim (pNonzero (pointer.symm.trans hp))
    · intro hp hz
      exact False.elim (lengthNonzero hz)
    · intro hp hz flags
      apply left_low_load e base hc _ (words[0]?.getD 0)
      · rw [pointer]
        have observed := stored.2.2.2 ⟨0, nonempty⟩
        change widthLoad s.dmem (p.toNat+8*0) 8 = some words[0].toNat at observed
        have first := widthLoad_eq s.dmem _ _ _ observed
        simpa only [NatOperand.pointer, Nat.mul_zero, Nat.add_zero,
          BitVec.ofNat_toNat, BitVec.setWidth_eq,
          List.getElem?_eq_getElem nonempty, Option.getD_some] using first
      · apply next
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- Finish the one-word input dispatch, then execute the concrete ADD/ADC site.
The original Large may still contain any number of redundant high zero words. -/
theorem right_low_sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (low : s.regs.rdx.toBitVec = SszNative.NatAdd.lowWord left)
    (pointer : s.regs.rcx.toBitVec = right.pointer)
    (payload : s.regs.r8.toBitVec = right.payload)
    (marker : (s.regs.r10.toBitVec.setWidth 8 = 0#8) ↔ right.pointer = 0#64)
    (stored : right.At (widthLoad s.dmem)) (nonzero : right.wordCount ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ t, SumReady s t left right → Eventually (step e) P (t, sumTarget left right base)) :
    Eventually (step e) P (s, base + 226) := by
  cases right with
  | small limb =>
    have markZero := marker.mpr rfl
    apply right_low_select e base hc s P
    intro flags
    rw [ite_eq_left markZero]
    refine (sum_sites_cps e base hc _ left (.small limb) rfl ?_ ?_ P ?_).1
    · exact low
    · simpa only [sumStart, SszNative.NatAdd.lowWord, NatOperand.words,
        List.getElem?_cons_zero, Option.getD_some, NatOperand.payload] using payload
    · intro t ready
      apply next t
      refine ⟨?_, ready.low, ready.high⟩
      exact ⟨ready.frame.memory, ready.frame.stack, ready.frame.output,
        ready.frame.arena, ready.frame.simd⟩
  | large p words =>
    have positive := stored.1
    have extent := stored.2.2.1
    have count := Limbs.sigWords_le_length words
    have nonempty : 0 < words.length := by
      change Limbs.sigWords words ≠ 0 at nonzero
      omega
    have pNonzero : p ≠ 0#64 := by intro hz; simp [hz] at positive
    have markNonzero : s.regs.r10.toBitVec.setWidth 8 ≠ 0#8 := by
      intro hz
      exact pNonzero (marker.mp hz)
    have lengthNonzero : s.regs.r8.toBitVec ≠ 0#64 := by
      rw [payload]
      change BitVec.ofNat 64 words.length ≠ 0#64
      bv_omega
    apply right_low_select e base hc s P
    intro flags
    rw [ite_eq_right markNonzero]
    apply right_low_load e base hc
    · intro hz
      exact False.elim (lengthNonzero hz)
    · intro hz flags
      apply right_low_loaded e base hc _ (words[0]?.getD 0)
      · change Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 =
          some ((words[0]?.getD 0).toNat : Int)
        rw [pointer]
        have observed := stored.2.2.2 ⟨0, nonempty⟩
        change widthLoad s.dmem (p.toNat+8*0) 8 = some words[0].toNat at observed
        have first := widthLoad_eq s.dmem _ _ _ observed
        simpa only [NatOperand.pointer, Nat.mul_zero, Nat.add_zero,
          BitVec.ofNat_toNat, BitVec.setWidth_eq,
          List.getElem?_eq_getElem nonempty, Option.getD_some] using first
      · refine (sum_sites_cps e base hc _ left (.large p words) rfl ?_ ?_ P ?_).2.1
        · exact low
        · rfl
        · intro t ready
          apply next t
          refine ⟨?_, ready.low, ready.high⟩
          exact ⟨ready.frame.memory, ready.frame.stack, ready.frame.output,
            ready.frame.arena, ready.frame.simd⟩

theorem one_word_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (marker : (s.regs.r10.toBitVec.setWidth 8 = 0#8) ↔ right.pointer = 0#64)
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem))
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ t, SumReady s t left right → Eventually (step e) P (t, sumTarget left right base)) :
    Eventually (step e) P (s, base + 209) := by
  apply left_low_cps e base hc s left leftPointer leftPayload leftAt leftNonzero P
  intro t loaded
  apply right_low_sum_cps e base hc t left right loaded.low
  · simpa only [loaded.pointer] using rightPointer
  · simpa only [loaded.payload] using rightPayload
  · simpa only [loaded.marker] using marker
  · simpa only [loaded.frame.memory] using rightAt
  · exact rightNonzero
  · intro u ready
    exact next u ⟨loaded.frame.trans ready.frame, ready.low, ready.high⟩

end SszX86.NatAdd
