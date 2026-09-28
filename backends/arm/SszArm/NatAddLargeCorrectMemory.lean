import SszArm.NatAddLargeLoopNative
import SszArm.NatAddSmallLoopNative
import SszArm.NatAddMaximum
import SszArm.NatAddArena
import SszArm.NatAddFirstWord
import SszArm.NatAddTransport
import SszArm.NatAddReturnValues
import SszArm.NatAddReturnError
import SszArm.NatAddNormalize

namespace SszArm.NatAdd.LargeCorrect

open SszNative
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Register frame of the complete allocating branch, including the allocator,
first-word dispatch, either carry loop, and output normalization. -/
structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5,
    reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 14#5, 15#5, 16#5, 17#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Frame.trans {s t u : ArmState} (st : Frame s t) (tu : Frame t u) : Frame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem Frame.sp {s t : ArmState} (frame : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem Frame.out {s t : ArmState} (frame : Frame s t) :
    r (.GPR 0#5) t = r (.GPR 0#5) s := frame.registers _ (by decide)

theorem Frame.code {s t : ArmState} (frame : Frame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by simpa only [CodeAt, frame.program] using hc

theorem Frame.aligned {s t : ArmState} (frame : Frame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem Frame.return_owned {s t : ArmState} (frame : Frame s t)
    (owned : ReturnOwned s) : ReturnOwned t := by
  exact ⟨by simpa only [frame.sp] using owned.stack,
    by simpa only [frame.out] using owned.output,
    by simpa only [frame.out, frame.sp] using owned.separate⟩

theorem Frame.returned {s t u : ArmState} (frame : Frame s t)
    (returned : Returned t u) : Returned s u := by
  refine ⟨returned.pc.trans (frame.registers _ (by decide)), returned.error,
    returned.sp.trans frame.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' constructor <;> bv_omega
  · intro reg low high
    rw [returned.vectors reg low high, frame.vectors reg]

theorem compare_frame {s t : ArmState} (frame : NatCompare.Frame s t)
    (out : r (.GPR 0#5) t = r (.GPR 0#5) s) : Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors⟩
  intro reg outside
  by_cases zero : reg = 0#5
  · subst reg; exact out
  · apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
    rcases outside with ⟨h8, h9, h10, h11, h12, _⟩
    exact ⟨zero, h8, h9, h10, h11, h12⟩

theorem arena_frame {s t : ArmState} (frame : ArenaFrame s t) : Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors⟩
  intro reg outside
  apply frame.registers
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
  rcases outside with ⟨h8, h9, h10, h11, h12, h13, _⟩
  exact ⟨h8, h9, h10, h11, h12, h13⟩

theorem first_frame {s t : ArmState} {kind : FirstKind} {base a b : BitVec 64}
    (frame : FirstWordPost kind s t base a b) : Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors⟩
  intro reg outside
  apply frame.registers
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
  rcases outside with ⟨_, _, _, h11, h12, h13, h14, h15, _⟩
  exact ⟨h11, h12, h13, h14, h15⟩

theorem loop_frame {writes : List Span} {s t : ArmState}
    (frame : LoopFrame writes s t) : Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors⟩
  intro reg outside
  apply frame.registers
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
  rcases outside with ⟨_, _, _, _, h12, h13, h14, h15, h16, h17⟩
  exact ⟨h12, h13, h14, h15, h16, h17⟩

/-- Span containment, rather than span identity, is the needed frame rule for
first-word stores and the two loops' progressively smaller writable suffixes. -/
theorem memory_of_contained {small large : List Span} {s t : ArmState}
    (frame : MemoryFrame small s t)
    (contained : ∀ inner ∈ small, ∃ outer ∈ large,
      outer.1 ≤ inner.1 ∧ inner.1 + inner.2 ≤ outer.1 + outer.2) :
    MemoryFrame large s t := by
  intro a outside
  apply frame a
  intro inner member
  obtain ⟨outer, member, low, high⟩ := contained inner member
  have separate := outside outer member
  omega

theorem protected_of_contained {small large : List Span} {address bytes : Nat}
    (owned : Protected large address bytes)
    (contained : ∀ inner ∈ small, ∃ outer ∈ large,
      outer.1 ≤ inner.1 ∧ inner.1 + inner.2 ≤ outer.1 + outer.2) :
    Protected small address bytes := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · right
    intro inner member
    obtain ⟨outer, member, low, high⟩ := contained inner member
    have apart := separate outer member
    omega

theorem words_at (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (stored : NatCompare.Words s pointer words) :
    NatMemory.wordsAt (widthLoad s) pointer.toNat words := by
  intro i
  have same := congrArg BitVec.toNat (stored i)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using congrArg some same

theorem fromWords_owned (writes : List Span) (pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Protected writes pointer.toNat (8 * words.length)) :
    OperandOwned writes (NatOperand.fromWords pointer words) := by
  have length : (Limbs.trim words).length ≤ words.length := by
    rw [Limbs.trim_length]; exact Limbs.sigWords_le_length words
  cases trimmed : Limbs.trim words with
  | nil => simp [NatOperand.fromWords, trimmed, OperandOwned]
  | cons first rest =>
    cases rest with
    | nil => simp [NatOperand.fromWords, trimmed, OperandOwned]
    | cons second rest =>
      simp only [NatOperand.fromWords, trimmed, OperandOwned]
      simpa only [Nat.add_zero] using owned.subspan 0 (8 * (first :: second :: rest).length)
        (by rw [trimmed] at length; omega)

/-- Physical original operands bound significant counts well below usize's end;
this is independent of the allocator's later signed layout guard. -/
theorem count_bound (s : ArmState) (operand : NatOperand)
    (input : operand.At (widthLoad s)) : operand.wordCount + 2 < 2^64 := by
  have count := Limbs.sigWords_le_length operand.words
  cases operand with
  | small word =>
    simp only [NatOperand.words, List.length_cons, List.length_nil] at count
    change Limbs.sigWords [word] + 2 < 2^64
    omega
  | large pointer words =>
    have physical := input.2.2.1
    change Limbs.sigWords words + 2 < 2^64
    simp only [NatOperand.words] at count
    omega

theorem written_nonzero (left right : NatOperand) (nonzero : left.wordCount ≠ 0) :
    Limbs.sigWords (SszNative.NatAdd.writtenWords left right) ≠ 0 := by
  intro zero
  have trimmed : Limbs.trim (SszNative.NatAdd.writtenWords left right) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa only [Limbs.trim_length] using zero
  have value := (Limbs.trim_eq_nil_iff_value_zero _).mp trimmed
  rw [SszNative.NatAdd.writtenWords_value] at value
  have leftZero : Limbs.value left.words = 0 := by
    change left.value = 0
    omega
  have empty := (Limbs.trim_eq_nil_iff_value_zero left.words).mpr leftZero
  apply nonzero
  rw [NatOperand.wordCount_eq_trim_length, empty]
  rfl

end SszArm.NatAdd.LargeCorrect
