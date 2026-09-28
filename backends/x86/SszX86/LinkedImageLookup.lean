module

public import SszX86.LinkedImageLayout
public import Kraken.X64.Syntax
public import Init.Data.List.TakeDrop

@[expose] public section

namespace SszX86.LinkedImage

abbrev Addressed := Int64 × Directive × Nat

/-- Exactly Kraken's first contiguous run at a PC, not a filter over all rows. -/
def lookup (rows : List Addressed) (pc : Int64) : List (Directive × Nat) :=
  ((rows.dropWhile (fun row => row.1 ≠ pc)).takeWhile
    (fun row => row.1 = pc)).map Prod.snd

@[simp] theorem lookup_nil (pc : Int64) : lookup [] pc = [] := rfl

theorem directivesAtAddress_eq_lookup (e : Executable) (pc : Int64) :
    e.directivesAtAddress pc = lookup e.withAddresses pc := rfl

theorem lookup_cons_of_ne (row : Addressed) (rows : List Addressed) (pc : Int64)
    (hne : row.1 ≠ pc) : lookup (row :: rows) pc = lookup rows pc := by
  simp [lookup, List.dropWhile, hne]

theorem lookup_cons_of_eq (row : Addressed) (rows : List Addressed) (pc : Int64)
    (heq : row.1 = pc) :
    lookup (row :: rows) pc =
      row.2 :: (rows.takeWhile (fun item => item.1 = pc)).map Prod.snd := by
  simp [lookup, List.dropWhile, heq]

/-- A prefix without this PC cannot affect where the first run starts. -/
theorem lookup_append_right (before rows : List Addressed) (pc : Int64)
    (hprefix : ∀ row ∈ before, row.1 ≠ pc) :
    lookup (before ++ rows) pc = lookup rows pc := by
  have hdrop := List.dropWhile_append_of_pos
    (p := fun row : Addressed => decide (row.1 ≠ pc)) (l₂ := rows)
    (fun row hr => by simpa using hprefix row hr)
  unfold lookup
  rw [hdrop]

theorem lookup_eq_nil (rows : List Addressed) (pc : Int64)
    (hrows : ∀ row ∈ rows, row.1 ≠ pc) : lookup rows pc = [] := by
  simpa only [List.append_nil, lookup_nil] using lookup_append_right rows [] pc hrows

private theorem takeWhile_append_no_match (rows suffix : List Addressed) (pc : Int64)
    (hsuffix : ∀ row ∈ suffix, row.1 ≠ pc) :
    (rows ++ suffix).takeWhile (fun row => row.1 = pc) =
      rows.takeWhile (fun row => row.1 = pc) := by
  induction rows with
  | nil =>
    cases suffix with
    | nil => rfl
    | cons row suffix =>
      have hne := hsuffix row (by simp)
      simp [List.takeWhile, hne]
  | cons row rows ih =>
    by_cases heq : row.1 = pc <;> simp [List.takeWhile, heq, ih]

/-- A suffix without this PC neither extends nor creates a matching run. -/
theorem lookup_append_left (rows suffix : List Addressed) (pc : Int64)
    (hsuffix : ∀ row ∈ suffix, row.1 ≠ pc) :
    lookup (rows ++ suffix) pc = lookup rows pc := by
  induction rows with
  | nil =>
    simpa only [List.nil_append, lookup_nil] using lookup_eq_nil suffix pc hsuffix
  | cons row rows ih =>
    by_cases heq : row.1 = pc
    · rw [List.cons_append, lookup_cons_of_eq row (rows ++ suffix) pc heq,
        lookup_cons_of_eq row rows pc heq, takeWhile_append_no_match rows suffix pc hsuffix]
    · simpa only [List.cons_append, lookup_cons_of_ne row (rows ++ suffix) pc heq,
        lookup_cons_of_ne row rows pc heq] using ih

theorem lookup_focus (before middle suffix : List Addressed) (pc : Int64)
    (hprefix : ∀ row ∈ before, row.1 ≠ pc)
    (hsuffix : ∀ row ∈ suffix, row.1 ≠ pc) :
    lookup (before ++ middle ++ suffix) pc = lookup middle pc := by
  simp only [List.append_assoc]
  rw [lookup_append_right before (middle ++ suffix) pc hprefix,
    lookup_append_left middle suffix pc hsuffix]

end SszX86.LinkedImage
