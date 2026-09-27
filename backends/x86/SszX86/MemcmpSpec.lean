import SszX86.MemcmpImpl
import SszX86.MemcpyExec

namespace SszX86.Memcmp

/-- Paired unsigned bytes, in increasing buffer-index order. -/
abbrev Bytes := List (BitVec 8 × BitVec 8)

/-- The C contract: subtract the first unequal unsigned bytes, otherwise zero. -/
def spec : Bytes → Int
  | [] => 0
  | (a, b) :: xs => if a = b then spec xs else (a.toNat : Int) - b.toNat

/-- Independent read observations, not separating ownership. Both views may
alias each other and the return slot. Empty views require no mapped pointer.
The Kraken instruction map is separate from this partial ordinary data memory. -/
def Reads (m : DataMem) (p q : BitVec 64) : Bytes → Prop
  | [] => True
  | (a, b) :: xs =>
      Mem.loadInt m p 1 = some (a.toNat : Int) ∧
      Mem.loadInt m q 1 = some (b.toNat : Int) ∧
      Reads m (p + 1) (q + 1) xs

/-- Every equal prefix is ignored. This links the loop's recurrence to the
first-difference, unsigned lexicographic specification. -/
theorem spec_equal_prefix (pre suffix : Bytes)
    (h : ∀ ab ∈ pre, ab.1 = ab.2) : spec (pre ++ suffix) = spec suffix := by
  induction pre with
  | nil => rfl
  | cons ab xs ih =>
    rcases ab with ⟨a, b⟩
    have hab : a = b := h (a, b) (by simp)
    rw [List.cons_append, spec, ite_eq_left hab]
    exact ih (fun ab hm => h ab (by simp [hm]))

theorem spec_first_difference (pre suffix : Bytes) (a b : BitVec 8)
    (h : ∀ ab ∈ pre, ab.1 = ab.2) (hne : a ≠ b) :
    spec (pre ++ (a, b) :: suffix) = (a.toNat : Int) - b.toNat := by
  rw [spec_equal_prefix pre _ h]
  simp [spec, hne]

theorem spec_all_equal (xs : Bytes) (h : ∀ ab ∈ xs, ab.1 = ab.2) : spec xs = 0 := by
  simpa only [List.append_nil, spec] using spec_equal_prefix xs [] h

/-- The signed low 32 bits, not the signed zero-extended 64-bit register. -/
theorem byte_difference (a b : BitVec 8) :
    (a.setWidth 32 - b.setWidth 32).toInt = (a.toNat : Int) - b.toNat := by
  have widen (v : BitVec 8) : (v.setWidth 32).toInt = (v.toNat : Int) := by
    rw [BitVec.toInt_setWidth]
    have hv := v.isLt
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [BitVec.toInt_sub, widen a, widen b]
  have ha := a.isLt
  have hb := b.isLt
  exact Int.bmod_eq_of_le (by omega) (by omega)

end SszX86.Memcmp
