import SszArm.NatAddLargeLoopBody

namespace SszArm.NatAdd.LargeLoop

open NatCompare (Words)
open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The exact writable suffix, excluding already-emitted words. -/
def suffixWrites (stack output : BitVec 64) (index remaining : Nat) : List Span :=
  [(stack.toNat - 16, 16), (output.toNat + 8 * index, 8 * remaining)]

def SuffixWords (s : ArmState) (output : BitVec 64) (index : Nat)
    (words : List (BitVec 64)) : Prop :=
  ∀ i : Fin words.length,
    read_mem_bytes 8 (output + BitVec.ofNat 64 (8 * (index + i.val))) s = words[i]

theorem SuffixWords.words {s : ArmState} {output : BitVec 64} {index : Nat}
    {words : List (BitVec 64)} (h : SuffixWords s output index words) :
    Words s (output + BitVec.ofNat 64 (8 * index)) words := by
  intro i
  have address : output + BitVec.ofNat 64 (8 * index) + BitVec.ofNat 64 (8 * i.val) =
      output + BitVec.ofNat 64 (8 * (index + i.val)) := by
    simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  rw [address]
  exact h i

theorem suffixProtected_next (stack output : BitVec 64) (index remaining address bytes : Nat)
    (owned : Protected (suffixWrites stack output index (remaining + 1)) address bytes) :
    Protected (suffixWrites stack output (index + 1) remaining) address bytes := by
  rcases owned with empty | apart
  · exact Or.inl empty
  · right
    intro span member
    simp only [suffixWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact apart _ (by simp [suffixWrites])
    · have separate := apart (output.toNat + 8 * index, 8 * (remaining + 1))
        (by simp [suffixWrites])
      simp only [Prod.fst, Prod.snd] at *
      omega

theorem suffixFrame_extend {s t : ArmState} (stack output : BitVec 64) (index remaining : Nat)
    (frame : LoopFrame (suffixWrites stack output (index + 1) remaining) s t) :
    LoopFrame (suffixWrites stack output index (remaining + 1)) s t := by
  refine ⟨frame.program, frame.error, frame.registers, frame.vectors, ?_⟩
  intro a outside
  apply frame.memory a
  intro span member
  simp only [suffixWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outside _ (by simp [suffixWrites])
  · have separate := outside (output.toNat + 8 * index, 8 * (remaining + 1))
      (by simp [suffixWrites])
    simp only [Prod.fst, Prod.snd] at *
    omega

/-- Widen the proved physical suffix frame into the caller's write footprint.
This does not require disjoint immutable inputs or an unused arena prefix. -/
theorem suffixFrame_into {s t : ArmState} (stack output : BitVec 64) (index remaining : Nat)
    (writes : List Span)
    (frame : LoopFrame (suffixWrites stack output index remaining) s t)
    (slot : (stack.toNat - 16, 16) ∈ writes)
    (outputCovered : ∀ a : BitVec 64,
      output.toNat + 8 * index ≤ a.toNat →
      a.toNat < output.toNat + 8 * (index + remaining) →
      ∃ span ∈ writes, span.1 ≤ a.toNat ∧ a.toNat < span.1 + span.2) :
    LoopFrame writes s t := by
  refine ⟨frame.program, frame.error, frame.registers, frame.vectors, ?_⟩
  intro a outside
  apply frame.memory a
  intro span member
  simp only [suffixWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outside _ slot
  · simp only [Prod.fst, Prod.snd]
    by_cases low : a.toNat < output.toNat + 8 * index
    · exact Or.inl low
    · by_cases high : output.toNat + 8 * index + 8 * remaining ≤ a.toNat
      · exact Or.inr high
      · obtain ⟨span, member, lo, hi⟩ := outputCovered a (by omega) (by omega)
        have := outside span member
        omega

theorem suffix_head_protected (stack output : BitVec 64) (index remaining : Nat)
    (separate : Protected [(stack.toNat - 16, 16)] output.toNat
      (8 * (index + remaining + 1))) :
    Protected (suffixWrites stack output (index + 1) remaining)
      (output.toNat + 8 * index) 8 := by
  have head := separate.subspan (8 * index) 8 (by omega)
  rcases head with empty | apart
  · omega
  · right
    intro span member
    simp only [suffixWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact apart _ (by simp)
    · simp only [Prod.fst, Prod.snd]
      omega

theorem suffix_words_cons (s : ArmState) (output first : BitVec 64) (index : Nat)
    (rest : List (BitVec 64))
    (head : read_mem_bytes 8 (output + BitVec.ofNat 64 (8 * index)) s = first)
    (tail : SuffixWords s output (index + 1) rest) :
    SuffixWords s output index (first :: rest) := by
  intro i
  cases hi : i.val with
  | zero => simpa [hi] using head
  | succ n =>
    have hn : n < rest.length := by have := i.isLt; simp only [List.length_cons] at this; omega
    have htail := tail ⟨n, hn⟩
    simpa [hi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

end SszArm.NatAdd.LargeLoop
