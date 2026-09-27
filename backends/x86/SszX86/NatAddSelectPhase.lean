import SszX86.NatAddSelect
import SszX86.NatAddLowWordPhase

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Both original operand pairs coexist with their independently scanned counts. -/
structure CountReady (s t : MachineData) (left right : NatOperand) : Prop where
  frame : ControlFrame s t
  left_pointer : t.regs.rsi.toBitVec = left.pointer
  left_payload : t.regs.rdx.toBitVec = left.payload
  right_pointer : t.regs.rcx.toBitVec = right.pointer
  right_payload : t.regs.r8.toBitVec = right.payload
  left_count : t.regs.rax.toBitVec = BitVec.ofNat 64 left.wordCount
  right_count : t.regs.r11.toBitVec = BitVec.ofNat 64 right.wordCount
  marker : (t.regs.r10.toBitVec.setWidth 8 = 0#8) ↔ right.pointer = 0#64

/-- The actual OR/CMP guard selects the exact ordered one-word or allocating
model branch, and one-word preparation executes its real loads and ADD/ADC. -/
theorem selection_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand)
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem))
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (ready : CountReady s t left right) (P : MachineState → Prop)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1 →
      ∀ u, SumReady s u left right → Eventually (step e) P (u, sumTarget left right base))
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1) →
      ∀ u, CountReady s u left right → Eventually (step e) P (u, base + 397)) :
    Eventually (step e) P (t, base + 193) := by
  have leftBound := operand_count_bound s.dmem left leftAt
  have rightBound := operand_count_bound s.dmem right rightAt
  have leftNat : t.regs.rax.toNat = left.wordCount := by
    change t.regs.rax.toBitVec.toNat = left.wordCount
    have eq := congrArg BitVec.toNat ready.left_count
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : left.wordCount < 2^64)] using eq
  have rightNat : t.regs.r11.toNat = right.wordCount := by
    change t.regs.r11.toBitVec.toNat = right.wordCount
    have eq := congrArg BitVec.toNat ready.right_count
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : right.wordCount < 2^64)] using eq
  apply size_select_cps e base hc t P
  intro flags
  have selected : CountReady s (sizeState t flags) left right := by
    refine ⟨ready.frame.trans ⟨rfl, rfl, rfl, rfl, rfl⟩,
      ready.left_pointer, ready.left_payload, ready.right_pointer, ready.right_payload,
      ready.left_count, ready.right_count, ready.marker⟩
  rw [leftNat, rightNat]
  by_cases fits : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
  · rw [ite_eq_left fits]
    apply one_word_cps e base hc _ left right selected.left_pointer selected.left_payload
      selected.right_pointer selected.right_payload selected.marker
    · simpa only [selected.frame.memory] using leftAt
    · simpa only [selected.frame.memory] using rightAt
    · exact leftNonzero
    · exact rightNonzero
    · intro u sum
      exact small fits u ⟨selected.frame.trans sum.frame, sum.low, sum.high⟩
  · rw [ite_eq_right fits]
    exact large fits _ selected

end SszX86.NatAdd
