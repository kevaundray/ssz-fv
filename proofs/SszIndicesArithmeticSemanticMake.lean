import SszIndicesArithmeticResources
import SszIndicesArithmeticSemanticWords

set_option autoImplicit false

namespace SszNative.Indices

theorem fillWords_pure (fill : Nat → BitVec 64) (position count : Nat) :
    fillWords (fun i (_ : Unit) => (fill i, ())) position count () =
      (List.ofFn (fun i : Fin count => fill (position + i.val)), ()) := by
  induction count generalizing position with
  | zero => simp [fillWords]
  | succ count ih =>
      have offsets : (fun i : Fin count => fill (position + 1 + i.val)) =
          (fun i : Fin count => fill (position + (i.val + 1))) := by
        funext i
        congr 1
        omega
      simp only [fillWords, ih, List.ofFn_succ, Fin.val_zero, Nat.add_zero,
        Fin.val_succ, offsets]

theorem makeNat_value (words base capacity used : Nat) (fill : Nat → BitVec 64)
    (result : NatOperand) (success : (makeNat words base capacity used fill).result = .ok result) :
    result.value = Limbs.value (List.ofFn (fun i : Fin words => fill i.val)) := by
  have value := makeNatState_success_value words base capacity used ()
    (fun i (_ : Unit) => (fill i, ())) result success
  simpa only [fillWords_pure, Nat.zero_add] using value

theorem makeNat_value_of_bits (words base capacity used number : Nat)
    (fill : Nat → BitVec 64) (result : NatOperand)
    (digits : ∀ position offset, offset < 64 →
      (fill position).getLsbD offset = number.testBit (64 * position + offset))
    (width : ∀ position, 64 * words ≤ position → number.testBit position = false)
    (success : (makeNat words base capacity used fill).result = .ok result) :
    result.value = number := by
  rw [makeNat_value words base capacity used fill result success]
  exact NatShift.generated_value words number fill digits width

theorem wordCount_covers (bits count : Nat) (success : wordCount bits = .ok count) :
    bits ≤ 64 * count := by
  unfold wordCount at success
  dsimp only at success
  by_cases checked :
      bits / 64 + (if bits % 64 = 0 then 0 else 1) < 2 ^ 64
  · simp only [checked, ↓reduceIte, Except.ok.injEq] at success
    subst count
    by_cases remainder : bits % 64 = 0 <;>
      simp only [remainder, ↓reduceIte] <;> omega
  · simp only [checked, ↓reduceIte] at success
    cases success

theorem wordCount_positive (bits count : Nat) (positive : 0 < bits)
    (success : wordCount bits = .ok count) : 0 < count := by
  have covers := wordCount_covers bits count success
  omega

end SszNative.Indices
