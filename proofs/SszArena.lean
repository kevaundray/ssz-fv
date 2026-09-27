import Std

set_option autoImplicit false

namespace SszNative.Arena

/- Pure arithmetic model of native/src/arena.rs:reserve::<u64> on a 64-bit
platform. `none` denotes ScratchExhausted. The model neither allocates memory
nor claims pointer provenance, memory writes, or native/ISA refinement. Storage
is owned by the caller; a successful result only describes its pointer and new
cursor. Failure has no returned cursor and does not commit an arena update. -/

structure Reservation where
  pointer : Nat
  used : Nat
  deriving DecidableEq, Repr

/-- Caller-owned storage and its current cursor, including the one-past-end bound. -/
def Valid (base capacity used : Nat) : Prop :=
  0 < base ∧ capacity < 2 ^ 63 ∧ base + capacity ≤ 2 ^ 64 ∧ used ≤ capacity

/-- Round an address upward to the alignment of a native `u64`. -/
def aligned (address : Nat) : Nat := ((address + 7) / 8) * 8

def padding (address : Nat) : Nat := aligned address - address

/-- Cursor after alignment, before reserving the actual words. -/
def start (base used : Nat) : Nat := used + padding (base + used)

/-- Cursor after both padding and the word payload have been consumed. -/
def finish (base used words : Nat) : Nat := start base used + 8 * words

/-- All failure guards of the positive-length native reservation. The checked
multiplication guard `8 * words < 2^64` is subsumed by the stricter isize guard
`8 * words < 2^63`. Combining these two is equivalent: both failures return
ScratchExhausted, and neither mutates the cursor. Every checked addition and the
capacity comparison remain explicit, even for inputs that are not valid arenas. -/
def Checks (base capacity used words : Nat) : Prop :=
  8 * words < 2 ^ 63 ∧
  base + used < 2 ^ 64 ∧
  base + used + 7 < 2 ^ 64 ∧
  start base used < 2 ^ 64 ∧
  finish base used words < 2 ^ 64 ∧
  finish base used words ≤ capacity

instance (base capacity used words : Nat) : Decidable (Checks base capacity used words) := by
  unfold Checks
  infer_instance

/-- Zero words use the aligned, non-null dangling pointer 8, without inspecting
any arena arithmetic. Positive words follow all checked arithmetic guards. -/
def reserve (base capacity used words : Nat) : Option Reservation :=
  if words = 0 then some ⟨8, used⟩
  else if Checks base capacity used words then
    some ⟨base + start base used, finish base used words⟩
  else none

/-- Required bytes fit after alignment, and their length fits positive isize. -/
def Fits (base capacity used words : Nat) : Prop :=
  8 * words < 2 ^ 63 ∧ padding (base + used) + 8 * words ≤ capacity - used

theorem aligned_bounds (address : Nat) :
    address ≤ aligned address ∧ aligned address ≤ address + 7 := by
  unfold aligned
  omega

theorem aligned_mod (address : Nat) : aligned address % 8 = 0 := by
  simp [aligned]

theorem padding_lt (address : Nat) : padding address < 8 := by
  have := aligned_bounds address
  unfold padding
  omega

theorem address_add_padding (address : Nat) :
    address + padding address = aligned address := by
  have := (aligned_bounds address).1
  unfold padding
  omega

theorem start_pointer (base used : Nat) :
    base + start base used = aligned (base + used) := by
  unfold start
  simpa only [Nat.add_assoc] using address_add_padding (base + used)

theorem used_le_start (base used : Nat) : used ≤ start base used := by
  unfold start
  omega

theorem finish_pointer (base used words : Nat) :
    aligned (base + used) + 8 * words = base + finish base used words := by
  rw [← start_pointer]
  simp only [finish, Nat.add_assoc]

/-- The checked multiplication cannot fail after the stricter length check. -/
theorem mul_and_isize_iff (words : Nat) :
    (8 * words < 2 ^ 64 ∧ 8 * words < 2 ^ 63) ↔ 8 * words < 2 ^ 63 := by
  omega

/-- Exact positive-length branch, with no validity assumptions. -/
theorem reserve_eq_some_iff_checks (base capacity used words : Nat)
    (positive : 0 < words) (r : Reservation) :
    reserve base capacity used words = some r ↔
      Checks base capacity used words ∧
        r = ⟨base + start base used, finish base used words⟩ := by
  have nonzero : words ≠ 0 := by omega
  by_cases checks : Checks base capacity used words
  · simp [reserve, nonzero, checks, eq_comm]
  · simp [reserve, nonzero, checks]

theorem reserve_eq_none_iff_checks (base capacity used words : Nat)
    (positive : 0 < words) :
    reserve base capacity used words = none ↔ ¬ Checks base capacity used words := by
  have nonzero : words ≠ 0 := by omega
  by_cases checks : Checks base capacity used words <;> simp [reserve, nonzero, checks]

/-- In valid storage, fitting a positive payload implies every overflow guard.
In particular, the at-least-eight payload bytes leave room for address + 7;
this is why the equivalence intentionally excludes zero-length reservations. -/
theorem checks_iff_fits (base capacity used words : Nat)
    (valid : Valid base capacity used) (positive : 0 < words) :
    Checks base capacity used words ↔ Fits base capacity used words := by
  rcases valid with ⟨base_pos, capacity_lt, storage_bound, cursor_bound⟩
  have align := aligned_bounds (base + used)
  have ptr := start_pointer base used
  have cursor := used_le_start base used
  unfold Checks Fits finish start
  constructor
  · rintro ⟨length, address, rounding, aligned_cursor, end_bound, fits⟩
    exact ⟨length, by omega⟩
  · rintro ⟨length, fits⟩
    refine ⟨length, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [start] at ptr cursor <;> omega

/-- Success iff the isize check holds and the aligned payload fits the remaining
caller storage. The result is uniquely the aligned address and exact new cursor. -/
theorem reserve_eq_some_iff (base capacity used words : Nat)
    (valid : Valid base capacity used) (positive : 0 < words) (r : Reservation) :
    reserve base capacity used words = some r ↔
      Fits base capacity used words ∧
        r = ⟨aligned (base + used), finish base used words⟩ := by
  rw [reserve_eq_some_iff_checks base capacity used words positive r,
    checks_iff_fits base capacity used words valid positive, start_pointer]

theorem success_iff (base capacity used words : Nat)
    (valid : Valid base capacity used) (positive : 0 < words) :
    (∃ r, reserve base capacity used words = some r) ↔ Fits base capacity used words := by
  constructor
  · rintro ⟨r, success⟩
    exact ((reserve_eq_some_iff base capacity used words valid positive r).1 success).1
  · intro fits
    exact ⟨⟨aligned (base + used), finish base used words⟩,
      (reserve_eq_some_iff base capacity used words valid positive _).2 ⟨fits, rfl⟩⟩

theorem exhausted_iff (base capacity used words : Nat)
    (valid : Valid base capacity used) (positive : 0 < words) :
    reserve base capacity used words = none ↔ ¬ Fits base capacity used words := by
  rw [reserve_eq_none_iff_checks base capacity used words positive,
    checks_iff_fits base capacity used words valid positive]

/-- Equivalent absolute-address form of the resource condition. -/
theorem fits_iff_storage (base capacity used words : Nat)
    (valid : Valid base capacity used) :
    Fits base capacity used words ↔
      8 * words < 2 ^ 63 ∧ aligned (base + used) + 8 * words ≤ base + capacity := by
  have cursor := valid.2.2.2
  have pointer := address_add_padding (base + used)
  unfold Fits
  omega

/-- Positive successful reservations are aligned and non-null, strictly consume
the cursor, and describe precisely an interval within the caller's storage.
The end may equal the one-past-end address 2^64; the returned pointer cannot. -/
theorem success_properties (base capacity used words : Nat)
    (valid : Valid base capacity used) (positive : 0 < words)
    (r : Reservation) (success : reserve base capacity used words = some r) :
    r.pointer % 8 = 0 ∧ 0 < r.pointer ∧ r.pointer < 2 ^ 64 ∧
      used < r.used ∧ r.used ≤ capacity ∧
      base + used ≤ r.pointer ∧
      r.pointer + 8 * words = base + r.used ∧
      r.pointer + 8 * words ≤ base + capacity ∧
      r.pointer + 8 * words ≤ 2 ^ 64 := by
  obtain ⟨fits, result⟩ :=
    (reserve_eq_some_iff base capacity used words valid positive r).1 success
  subst r
  rcases valid with ⟨base_pos, capacity_lt, storage_bound, cursor_bound⟩
  have align := aligned_bounds (base + used)
  have ptr := finish_pointer base used words
  have cursor := used_le_start base used
  rcases fits with ⟨length, fits⟩
  dsimp only
  refine ⟨aligned_mod _, ?_, ?_, ?_, ?_, ?_, ptr, ?_, ?_⟩ <;>
    dsimp [finish, start] at * <;> omega

/-- Committing a successful cursor preserves the caller-arena invariant. -/
theorem valid_after_success (base capacity used words : Nat)
    (valid : Valid base capacity used) (r : Reservation)
    (success : reserve base capacity used words = some r) :
    Valid base capacity r.used := by
  by_cases zero : words = 0
  · subst words
    have result : (⟨8, used⟩ : Reservation) = r := by
      simpa [reserve] using success
    subst r
    exact valid
  · have properties := success_properties base capacity used words valid (by omega) r success
    exact ⟨valid.1, valid.2.1, valid.2.2.1, properties.2.2.2.2.1⟩

/-- Empty reservations have no arena precondition, consume no padding, and do
not check otherwise overflowing or out-of-capacity arena arithmetic. -/
@[simp] theorem reserve_zero (base capacity used : Nat) :
    reserve base capacity used 0 = some ⟨8, used⟩ := by
  simp [reserve]

theorem reserve_zero_properties (base capacity used : Nat) (r : Reservation)
    (success : reserve base capacity used 0 = some r) :
    r.pointer = 8 ∧ r.pointer % 8 = 0 ∧ 0 < r.pointer ∧ r.used = used := by
  have result : (⟨8, used⟩ : Reservation) = r := by
    simpa using success
  subst r
  simp

/-- The native `from_le_bytes` word count, extended to empty inputs. -/
def wordsForBytes (count : Nat) : Nat :=
  if count = 0 then 0 else 1 + (count - 1) / 8

theorem wordsForBytes_eq (count : Nat) : wordsForBytes count = (count + 7) / 8 := by
  unfold wordsForBytes
  split <;> omega

theorem wordsForBytes_bounds (count : Nat) :
    count ≤ 8 * wordsForBytes count ∧ 8 * wordsForBytes count ≤ count + 7 := by
  rw [wordsForBytes_eq]
  omega

/-- With the native input-length bound, optimized word-byte multiplication
cannot overflow usize. The stricter isize guard is still required. -/
theorem wordsForBytes_bytes_lt (count : Nat) (bound : count < 2 ^ 63) :
    8 * wordsForBytes count < 2 ^ 64 := by
  have := wordsForBytes_bounds count
  omega

/-- Clearing the low three bits is division then multiplication by eight.
This uses the kernel's shift/mask theorem, not bit-blasting or a SAT oracle. -/
theorem mask_toNat (value : BitVec 64) :
    (value &&& ~~~(7 : BitVec 64)).toNat = value.toNat / 8 * 8 := by
  have mask : (~~~(7 : BitVec 64)) = BitVec.allOnes 64 <<< 3 := by decide
  rw [mask, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (value.toNat / 8 * 8) % 2 ^ 64 = value.toNat / 8 * 8
  apply Nat.mod_eq_of_lt
  have := value.isLt
  omega

/-- The native mask-rounding expression equals mathematical alignment exactly
when its checked addition succeeds. -/
theorem mask_rounding (address : BitVec 64) (no_overflow : address.toNat + 7 < 2 ^ 64) :
    ((address + 7) &&& ~~~(7 : BitVec 64)).toNat = aligned address.toNat := by
  rw [mask_toNat, BitVec.toNat_add]
  change ((address.toNat + 7) % 2 ^ 64) / 8 * 8 = aligned address.toNat
  rw [Nat.mod_eq_of_lt no_overflow]
  rfl

/-- The lowered high-bit mask is exactly the native positive-isize length check. -/
theorem high_bit_clear (bytes : BitVec 64) :
    bytes &&& (BitVec.ofNat 64 (2^63)) = 0#64 ↔ bytes.toNat < 2^63 := by
  have mask : BitVec.ofNat 64 (2^63) = BitVec.allOnes 64 <<< 63 := by decide
  have value : (bytes &&& BitVec.ofNat 64 (2^63)).toNat =
      bytes.toNat / 2^63 * 2^63 := by
    rw [mask, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    have := bytes.isLt
    omega
  rw [← BitVec.toNat_inj, value]
  simp only [BitVec.toNat_ofNat]
  omega

end SszNative.Arena
