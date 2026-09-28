module

public import SszX86.LinkedImageLayout

@[expose] public section

namespace SszX86.LinkedImage

/-- Check only addresses and widths, never compare instruction or data payloads. -/
def hasSequentialAddresses {D : Type} (start : Int64) : List (Int64 × D × Nat) → Bool
  | [] => true
  | (pc, _, byteWidth) :: rows =>
    (pc == start) && hasSequentialAddresses (start + Int64.ofNat byteWidth) rows

/-- Erasing certified addresses reconstructs the exact executable layout. -/
theorem withAddresses_of_sequential {D : Type} (start : Int64)
    (rows : List (Int64 × D × Nat))
    (checked : hasSequentialAddresses start rows = true) :
    Kraken.Executable.withAddresses (start, rows.map Prod.snd) = rows := by
  induction rows generalizing start with
  | nil => simp only [List.map_nil, Kraken.Executable.withAddresses]
  | cons row rows ih =>
    rcases row with ⟨pc, directive, byteWidth⟩
    simp only [hasSequentialAddresses, Bool.and_eq_true, beq_iff_eq] at checked
    rcases checked with ⟨same, rest⟩
    subst start
    simpa only [List.map_cons, Kraken.Executable.withAddresses] using
      congrArg (List.cons (pc, directive, byteWidth))
        (ih (pc + Int64.ofNat byteWidth) rest)

end SszX86.LinkedImage
