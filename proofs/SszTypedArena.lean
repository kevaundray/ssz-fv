import SszArena

set_option autoImplicit false

namespace SszNative.TypedArena

/-- Native element layout; alignment is a power of two by construction.
This arithmetic model does not establish a Rust type's layout or pointer provenance. -/
structure Layout where
  size : Nat
  alignLog2 : Nat
  deriving DecidableEq, Repr

def Layout.alignment (layout : Layout) : Nat := 2 ^ layout.alignLog2

def aligned (layout : Layout) (address : Nat) : Nat :=
  ((address + (layout.alignment - 1)) / layout.alignment) * layout.alignment

def padding (layout : Layout) (address : Nat) : Nat := aligned layout address - address

def start (layout : Layout) (base used : Nat) : Nat :=
  used + padding layout (base + used)

def finish (layout : Layout) (base used count : Nat) : Nat :=
  start layout base used + layout.size * count

/-- The checked multiplication is subsumed by the stricter positive-isize bound.
All addition guards and the final capacity guard remain explicit. -/
def Checks (layout : Layout) (base capacity used count : Nat) : Prop :=
  layout.size * count < 2 ^ 63 ∧
  base + used < 2 ^ 64 ∧
  base + used + (layout.alignment - 1) < 2 ^ 64 ∧
  start layout base used < 2 ^ 64 ∧
  finish layout base used count < 2 ^ 64 ∧
  finish layout base used count ≤ capacity

instance (layout : Layout) (base capacity used count : Nat) :
    Decidable (Checks layout base capacity used count) := by
  unfold Checks
  infer_instance

/-- `reserve<T>` checks zero length/zero-sized elements before inspecting arena
arithmetic. A successful positive reservation commits before any initializer.
Initialization and its possibly retained partial effects belong to the caller. -/
def reserve (layout : Layout) (base capacity used count : Nat) : Option Arena.Reservation :=
  if count = 0 ∨ layout.size = 0 then some ⟨layout.alignment, used⟩
  else if Checks layout base capacity used count then
    some ⟨base + start layout base used, finish layout base used count⟩
  else none

theorem alignment_pos (layout : Layout) : 0 < layout.alignment :=
  Nat.pow_pos (by decide)

theorem aligned_bounds (layout : Layout) (address : Nat) :
    address ≤ aligned layout address ∧
      aligned layout address ≤ address + (layout.alignment - 1) := by
  have positive := alignment_pos layout
  have remainder := Nat.mod_lt (address + (layout.alignment - 1)) positive
  have decomposition := Nat.div_add_mod (address + (layout.alignment - 1)) layout.alignment
  rw [Nat.mul_comm] at decomposition
  unfold aligned
  omega

theorem aligned_mod (layout : Layout) (address : Nat) :
    aligned layout address % layout.alignment = 0 := by
  simp only [aligned, Nat.mul_mod_left]

theorem padding_lt (layout : Layout) (address : Nat) :
    padding layout address < layout.alignment := by
  have := aligned_bounds layout address
  have := alignment_pos layout
  unfold padding
  omega

theorem start_pointer (layout : Layout) (base used : Nat) :
    base + start layout base used = aligned layout (base + used) := by
  have := (aligned_bounds layout (base + used)).1
  unfold start padding
  omega

theorem used_le_finish (layout : Layout) (base used count : Nat) :
    used ≤ finish layout base used count := by
  unfold finish start
  omega

theorem reserve_zero (layout : Layout) (base capacity used : Nat) :
    reserve layout base capacity used 0 = some ⟨layout.alignment, used⟩ := by
  simp only [reserve, true_or, ↓reduceIte]

theorem reserve_zero_sized (layout : Layout) (base capacity used count : Nat)
    (zero : layout.size = 0) :
    reserve layout base capacity used count = some ⟨layout.alignment, used⟩ := by
  simp only [reserve, zero, or_true, ↓reduceIte]

theorem reserve_positive (layout : Layout) (base capacity used count : Nat)
    (countPositive : 0 < count) (sizePositive : 0 < layout.size) :
    reserve layout base capacity used count =
      if Checks layout base capacity used count then
        some ⟨base + start layout base used, finish layout base used count⟩ else none := by
  have countNonzero := Nat.ne_of_gt countPositive
  have sizeNonzero := Nat.ne_of_gt sizePositive
  simp only [reserve, countNonzero, sizeNonzero, false_or, ↓reduceIte]

theorem reserve_cursor_bounds (layout : Layout) (base capacity used count : Nat)
    (valid : Arena.Valid base capacity used) (result : Arena.Reservation)
    (success : reserve layout base capacity used count = some result) :
    used ≤ result.used ∧ result.used ≤ capacity := by
  unfold reserve at success
  split at success
  · cases success
    exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · split at success
    · rename_i checked
      cases success
      exact ⟨used_le_finish layout base used count, checked.2.2.2.2.2⟩
    · cases success

/-- Exact cutover bridge to the already checked eight-byte reservation model. -/
theorem reserve_u64 (base capacity used count : Nat) :
    reserve ⟨8, 3⟩ base capacity used count = Arena.reserve base capacity used count := by
  simp only [reserve, Layout.alignment, Checks, finish, start, padding, aligned,
    Arena.reserve, Arena.Checks, Arena.finish, Arena.start, Arena.padding, Arena.aligned,
    Nat.reducePow, Nat.reduceSub, Nat.reduceEqDiff, or_false] <;> rfl

/-- Forty-byte, eight-aligned Plan payloads share the existing exact guards;
this does not reinterpret a checked usize multiplication as wrapping arithmetic. -/
theorem reserve_forty (base capacity used count : Nat) :
    reserve ⟨40, 3⟩ base capacity used count =
      Arena.reserve base capacity used (5 * count) := by
  have scaled : 8 * (5 * count) = 40 * count := by omega
  simp only [reserve, Layout.alignment, Checks, finish, start, padding, aligned,
    Arena.reserve, Arena.Checks, Arena.finish, Arena.start, Arena.padding, Arena.aligned,
    Nat.reducePow, Nat.reduceSub, Nat.reduceEqDiff, or_false, Nat.mul_eq_zero,
    false_or, scaled] <;> rfl

end SszNative.TypedArena
