import SszX86.Udivti3Math

namespace SszX86.WordNormalize

/-- Keep machine register expressions in the bit-vector representation used by
instruction summaries. These rules are opt-in: the global simp set deliberately
normalizes in the opposite direction and must not be mixed into this pass. -/
theorem numeral (n : Nat) : (OfNat.ofNat n : UInt64) = UInt64.ofBitVec (BitVec.ofNat 64 n) := rfl

theorem ofNat (n : Nat) : UInt64.ofNat n = UInt64.ofBitVec (BitVec.ofNat 64 n) := rfl

theorem add (a b : UInt64) : a+b = UInt64.ofBitVec (a.toBitVec+b.toBitVec) := rfl

theorem natView (a : UInt64) : a.toNat = a.toBitVec.toNat := rfl

theorem bitvecNumeral (n : Nat) : (OfNat.ofNat n : BitVec 64) = BitVec.ofNat 64 n := rfl

theorem resultCarry {w : Nat} (value : BitVec w) (flags : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result value flags).cf = flags.cf := rfl

/-- Normalize both a continuation and the decoded state with the same directed
rules. Carry arithmetic reuses the checked ADD summary; this is simplification,
not a decision oracle. The caller supplies only its local state definitions. -/
macro "word_simpa " "[" defs:Lean.Parser.Tactic.simpArg,* "]" " using " proof:term : tactic => do
  let args : Lean.TSyntaxArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] :=
    defs.getElems.map (fun arg => ⟨arg.raw⟩)
  let canonical ← `(Lean.Parser.Tactic.simpArgs|
    [SszX86.WordNormalize.numeral, SszX86.WordNormalize.ofNat,
      SszX86.WordNormalize.add, SszX86.WordNormalize.natView,
      SszX86.WordNormalize.bitvecNumeral, UInt64.toBitVec_ofBitVec,
      UInt64.ofBitVec_toBitVec, SszX86.Udivti3.addFlags_cf, SszX86.WordNormalize.resultCarry,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero, BitVec.zero_add,
      Nat.add_zero, Nat.zero_add, Bool.toNat_false, Bool.toNat_true,
      BitVec.add_comm, Nat.add_comm, BitVec.toInt_add, Int.add_comm])
  match canonical with
  | `(Lean.Parser.Tactic.simpArgs| [$rules,*]) =>
    let allArgs := args ++ rules.getElems
    `(tactic| simpa (config := {instances := true}) only [$allArgs,*] using $proof)
  | _ => Lean.Macro.throwUnsupported

end SszX86.WordNormalize
