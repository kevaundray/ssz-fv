import SszArm.NatMulNormalizeSelect
import SszArm.NatMulReturnOutput

namespace SszArm.NatMul

open UintCodec SszNative.Limbs
open Delimited (Protected MemoryFrame Returned)

/-- Canonicalization retains at most the original initialized span. -/
theorem normalized_output_owned (writes : List Delimited.Span) (pointer : BitVec 64)
    (words : List (BitVec 64)) (protected : Protected writes pointer.toNat (8 * words.length)) :
    NatAdd.OperandOwned writes (SszNative.NatOperand.fromWords pointer words) := by
  have length : (trim words).length ≤ words.length := by
    rw [trim_length]
    exact sigWords_le_length words
  cases trimmed : trim words with
  | nil => simp only [SszNative.NatOperand.fromWords, trimmed, NatAdd.OperandOwned]
  | cons first rest =>
    cases rest with
    | nil => simp only [SszNative.NatOperand.fromWords, trimmed, NatAdd.OperandOwned]
    | cons second rest =>
      simp only [SszNative.NatOperand.fromWords, trimmed, NatAdd.OperandOwned]
      have sub := protected.subspan 0 (8 * (first :: second :: rest).length)
        (by simp only [trimmed] at length; omega)
      simpa only [Nat.add_zero] using sub

/-- The exact allocated words survive the backward scan, representation choice,
result stores, saved-register reloads and original RET. -/
theorem normalize_return_run (entry s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1060#64) (saved : Saved entry s)
    (space : ReturnSpace s (r (.GPR 24#5) s))
    (output : r (.GPR 20#5) s = pointer)
    (count : r (.GPR 23#5) s = BitVec.ofNat 64 words.length - 1#64)
    (source : NatCompare.Source s pointer words) (memory : NatCompare.Words s pointer words)
    (nonnull : 0 < pointer.toNat) (wordAligned : pointer.toNat % 8 = 0)
    (protected : Protected (returnWrites s (r (.GPR 24#5) s)) pointer.toNat (8 * words.length)) :
    ∃ fuel t, run fuel s = t ∧ Returned entry t ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 24#5) s).toNat
        (.ok (SszNative.NatOperand.fromWords pointer words)) ∧
      SszNative.NatMemory.wordsAt (widthLoad t) pointer.toNat words ∧
      MemoryFrame (returnWrites s (r (.GPR 24#5) s)) s t := by
  have rawAt : (SszNative.NatOperand.large pointer words).At (widthLoad s) := by
    refine ⟨nonnull, wordAligned, source.2.1, ?_⟩
    intro i
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using
      congrArg (fun word : BitVec 64 => some word.toNat) (memory i)
  obtain ⟨fuel, u, hu, huf, hup, hu20, hu8⟩ :=
    normalize_ready s base pointer words code error aligned pc output count source memory
  have hu24 : r (.GPR 24#5) u = r (.GPR 24#5) s := huf.registers _ (by decide)
  have writes : returnWrites u (r (.GPR 24#5) u) = returnWrites s (r (.GPR 24#5) s) := by
    simp only [returnWrites, hu24, huf.sp]
  have rawAtU : (SszNative.NatOperand.large pointer words).At (widthLoad u) :=
    NatAdd.operand_at_preserved (huf.frame (r (.GPR 24#5) s)) _ rawAt protected
  have ownedU : NatAdd.OperandOwned (returnWrites u (r (.GPR 24#5) u))
      (SszNative.NatOperand.fromWords pointer words) := by
    rw [writes]
    exact normalized_output_owned _ pointer words protected
  obtain ⟨ht, returned, image, tailFrame⟩ := output_return_run entry u base
    (huf.code code) (huf.error.trans error) (huf.aligned aligned) hup
    (huf.saved saved space) (by simpa only [hu24] using huf.space space)
    (SszNative.NatOperand.fromWords pointer words) hu20 hu8
    (SszNative.NatOperand.fromWords_at _ pointer words rawAtU) ownedU
  have frame : MemoryFrame (returnWrites s (r (.GPR 24#5) s)) s (outputReturned u base) := by
    rw [writes] at tailFrame
    exact (huf.frame _).trans tailFrame
  refine ⟨fuel + 19, outputReturned u base, ?_, returned, ?_, ?_, frame⟩
  · rw [run_plus, hu, ht]
  · simpa only [hu24] using image
  · exact (NatAdd.operand_at_preserved frame (.large pointer words) rawAt protected).2.2.2

/-- Adapter for the successful loop's exact initialized allocation, not an
assumption about the eventual returned result or its memory. -/
theorem normalize_committed_return (entry s : ArmState) (base : BitVec 64)
    (reservation : SszNative.Arena.Reservation) (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1060#64) (saved : Saved entry s)
    (space : ReturnSpace s (r (.GPR 24#5) s))
    (output : r (.GPR 20#5) s = BitVec.ofNat 64 reservation.pointer)
    (count : r (.GPR 23#5) s = BitVec.ofNat 64 words.length - 1#64)
    (physical : reservation.pointer + 8 * words.length ≤ 2^64)
    (nonnull : 0 < reservation.pointer) (wordAligned : reservation.pointer % 8 = 0)
    (addressBound : reservation.pointer < 2^64)
    (initialized : SszNative.NatMemory.wordsAt (widthLoad s) reservation.pointer words)
    (protected : Protected (returnWrites s (r (.GPR 24#5) s)) reservation.pointer (8 * words.length)) :
    ∃ fuel t, run fuel s = t ∧ Returned entry t ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 24#5) s).toNat
        (SszNative.NatArithmetic.committed reservation words).result ∧
      NatAdd.WrittenAt (widthLoad t) (SszNative.NatArithmetic.committed reservation words) ∧
      MemoryFrame (returnWrites s (r (.GPR 24#5) s)) s t := by
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound]
  have source : NatCompare.Source s (BitVec.ofNat 64 reservation.pointer) words := by
    refine ⟨space.stack, by simpa only [pointerNat] using physical, ?_⟩
    rcases protected with empty | separate
    · left
      apply List.eq_nil_of_length_eq_zero
      omega
    · right
      have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [returnWrites])
      simp only [Prod.fst, Prod.snd] at apart
      have := space.stack
      simpa only [pointerNat] using (show reservation.pointer + 8 * words.length ≤
        (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ reservation.pointer by omega)
  have memory : NatCompare.Words s (BitVec.ofNat 64 reservation.pointer) words := by
    intro i
    apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add] using Option.some.inj (initialized i)
  obtain ⟨fuel, t, run, returned, image, written, frame⟩ := normalize_return_run entry s base
    (BitVec.ofNat 64 reservation.pointer) words code error aligned pc saved space output count
    source memory (by simpa only [pointerNat] using nonnull)
    (by simpa only [pointerNat] using wordAligned)
    (by simpa only [pointerNat] using protected)
  refine ⟨fuel, t, run, returned, image, ?_, frame⟩
  intro allocated same
  have equal : reservation = allocated := Option.some.inj same
  subst allocated
  simpa only [pointerNat] using written

end SszArm.NatMul
