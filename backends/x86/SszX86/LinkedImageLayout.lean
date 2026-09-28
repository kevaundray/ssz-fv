module

public import Kraken.Layout
public import Init.Data.SInt.Lemmas

@[expose] public section

namespace SszX86.LinkedImage

/-- Total byte width, with the same modular address arithmetic as Kraken. -/
def width {D : Type} : List (D × Nat) → Int64
  | [] => 0
  | (_, size) :: rows => Int64.ofNat size + width rows

@[simp] theorem width_nil {D : Type} : width ([] : List (D × Nat)) = 0 := rfl

@[simp] theorem width_cons {D : Type} (directive : D) (size : Nat)
    (rows : List (D × Nat)) :
    width ((directive, size) :: rows) = Int64.ofNat size + width rows := rfl

theorem width_append {D : Type} (xs ys : List (D × Nat)) :
    width (xs ++ ys) = width xs + width ys := by
  induction xs with
  | nil => simp [width]
  | cons row xs ih =>
    rcases row with ⟨directive, size⟩
    simp [width, ih, Int64.add_assoc]

/-- Concatenation preserves every directive, including zero-width label runs. -/
theorem withAddresses_append {D : Type} (xs ys : List (D × Nat)) (start : Int64) :
    Kraken.Executable.withAddresses (start, xs ++ ys) =
      Kraken.Executable.withAddresses (start, xs) ++
      Kraken.Executable.withAddresses (start + width xs, ys) := by
  induction xs generalizing start with
  | nil => simp [Kraken.Executable.withAddresses, width]
  | cons row xs ih =>
    rcases row with ⟨directive, size⟩
    simp only [List.cons_append, Kraken.Executable.withAddresses, width, ih,
      Int64.add_assoc]

/-- Compose opaque chunk certificates without evaluating either chunk again. -/
theorem withAddresses_append_of_eq {D : Type} (xs ys : List (D × Nat))
    (start total : Int64) (left right : List (Int64 × D × Nat))
    (hwidth : width xs = total)
    (hleft : Kraken.Executable.withAddresses (start, xs) = left)
    (hright : Kraken.Executable.withAddresses (start + total, ys) = right) :
    Kraken.Executable.withAddresses (start, xs ++ ys) = left ++ right := by
  rw [withAddresses_append, hleft, hwidth, hright]

end SszX86.LinkedImage
