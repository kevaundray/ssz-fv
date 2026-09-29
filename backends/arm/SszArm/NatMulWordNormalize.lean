import SszArm.NatMulWordNormalizeSelect

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs
open Delimited (Protected MemoryFrame Returned)

/-- Physical ownership at row1464. The current buffer is supplied separately as
Words; neither the normalized result nor any future limb observation is assumed. -/
structure NormalizeOwned (s : ArmState) (pointer : BitVec 64)
    (words : List (BitVec 64)) : Prop where
  returns : ReturnOwned s
  positive : 0 < pointer.toNat
  aligned : pointer.toNat % 8 = 0
  physical : pointer.toNat + 8 * words.length ≤ 2^64
  separate : Protected (valueWrites s) pointer.toNat (8 * words.length)

theorem NormalizeOwned.source {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : NormalizeOwned s pointer words) :
    NatCompare.Source s pointer words := by
  refine ⟨owned.returns.stack, owned.physical, ?_⟩
  rcases owned.separate with empty | separate
  · left
    apply List.eq_nil_of_length_eq_zero
    omega
  · right
    have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16)
      (by simp [valueWrites, NatAdd.valueWrites])
    have stack := owned.returns.stack
    arm_word_nf at apart stack ⊢
    omega

theorem NormalizeOwned.current_at {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : NormalizeOwned s pointer words)
    (current : NatCompare.Words s pointer words) :
    (SszNative.NatOperand.large pointer words).At (widthLoad s) := by
  refine ⟨owned.positive, owned.aligned, owned.physical, ?_⟩
  intro i
  have word := congrArg (fun w : BitVec 64 => some w.toNat) (current i)
  simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using word

/-- Exact successful result and writable footprint. The frame preserves the
arena cursor, complete original input extents (including redundant zeros), all
allocation bytes, and output padding whenever those extents are protected.
Only the descriptor pair, status32, and actual sixteen-byte spill are writable. -/
structure NormalizedReturn (s t : ArmState) (pointer : BitVec 64)
    (limbs : List (BitVec 64)) : Prop where
  returned : Returned s t
  image : SszNative.NatArithmetic.AddResultAt (widthLoad t)
    (r (.GPR 0#5) s).toNat (.ok (SszNative.NatOperand.fromWords pointer limbs))
  frame : MemoryFrame (valueWrites s) s t
  words : NatCompare.Words t pointer limbs
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  spills : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) t = normalizeSpill s pointer limbs ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) t = pointer
  padding : ∀ a : BitVec 64,
    (((r (.GPR 0#5) s).toNat + 16 ≤ a.toNat ∧ a.toNat < (r (.GPR 0#5) s).toNat + 64) ∨
      ((r (.GPR 0#5) s).toNat + 68 ≤ a.toNat ∧ a.toNat < (r (.GPR 0#5) s).toNat + 72)) →
    t.mem a = s.mem a

/-- Actual row1464 through RET1540 or RET1628, for an arbitrary complete written
image. The backward scan is unbounded Nat induction; only physical nonwrapping
ownership bounds the machine representation of its counter. -/
theorem normalize_run_contract (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1464#64)
    (h8 : r (.GPR 8#5) s = -BitVec.ofNat 64 (8 * (words.length - 1)))
    (h10 : r (.GPR 10#5) s = pointer)
    (h11 : r (.GPR 11#5) s = words[0]?.getD 0#64)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 (words.length + 1))
    (owned : NormalizeOwned s pointer words) (current : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NormalizedReturn s t pointer words := by
  obtain ⟨fuel, u, hu, huf, hup, pointerEq, payloadEq, hu9⟩ := normalize_ready s base pointer words
    hc he ha hp h8 h10 h11 h12 owned.source current
  let path := normalizePath words
  let operand := SszNative.NatOperand.fromWords pointer words
  have rawAt := owned.current_at current
  have atU : operand.At (widthLoad u) := by
    rw [huf.loads]
    exact SszNative.NatOperand.fromWords_at (widthLoad s) pointer words rawAt
  have protectedU : NatAdd.OperandOwned (valueWrites u) operand := by
    rw [huf.writes]
    exact NatAdd.fromWords_owned _ pointer words owned.separate
  obtain ⟨ht, returned, image, frame⟩ := value_run_contract path u base
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup (huf.owned owned.returns)
    operand pointerEq payloadEq atU protectedU
  let t := valueResult path base u
  have memory : MemoryFrame (valueWrites s) s t := by
    intro a outside
    exact (frame a (by simpa only [huf.writes] using outside)).trans (congrFun huf.memory a)
  have rawFinal := NatAdd.operand_at_preserved memory
    (.large pointer words) rawAt owned.separate
  have spills := value_spills path u base (huf.owned owned.returns)
  have hu10 : r (.GPR 10#5) u = pointer := (huf.registers _ (by decide)).trans h10
  refine ⟨fuel + ((valueOps path).length + 11), t, ?_, ?_⟩
  · rw [run_plus, hu, ht]
  · refine ⟨huf.returned returned, ?_, memory, ?_, ?_, ?_, ?_⟩
    · simpa only [huf.out] using image
    · intro i
      apply BitVec.eq_of_toNat_eq
      have word := Option.some.inj (rawFinal.2.2.2 i)
      simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using word
    · intro reg keep
      exact (value_registers path u base (huf.owned owned.returns) reg).trans (huf.registers reg keep)
    · simpa only [huf.sp, hu9, hu10] using spills
    · intro a padding
      have preserved := value_padding path u base (huf.owned owned.returns) a
        (by simpa only [huf.out] using padding)
      exact preserved.trans (congrFun huf.memory a)

/-- The allocating mul_word caller supplies exactly c+1 words from the shared
recurrence. Its last zero-extended multiplication step and carry are not trimmed
before the machine scan. Normalization retains the allocation pointer iff more
than one significant word remains. -/
theorem normalize_word_run_contract (s : ArmState) (base pointer factor : BitVec 64)
    (operand : SszNative.NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1464#64)
    (h8 : r (.GPR 8#5) s = -BitVec.ofNat 64 (8 * operand.wordCount))
    (h10 : r (.GPR 10#5) s = pointer)
    (h11 : r (.GPR 11#5) s = (SszNative.NatMul.wordWritten operand factor)[0]?.getD 0#64)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 (operand.wordCount + 2))
    (owned : NormalizeOwned s pointer (SszNative.NatMul.wordWritten operand factor))
    (current : NatCompare.Words s pointer (SszNative.NatMul.wordWritten operand factor)) :
    ∃ fuel t, run fuel s = t ∧
      NormalizedReturn s t pointer (SszNative.NatMul.wordWritten operand factor) := by
  apply normalize_run_contract s base pointer (SszNative.NatMul.wordWritten operand factor)
    hc he ha hp _ h10 h11 _ owned current
  · simpa only [SszNative.NatMul.wordWritten_length, Nat.add_sub_cancel] using h8
  · simpa only [SszNative.NatMul.wordWritten_length, Nat.add_assoc] using h12

end SszArm.NatMulWord
