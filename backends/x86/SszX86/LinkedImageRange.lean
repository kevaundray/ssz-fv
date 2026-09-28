module

public import SszX86.LinkedImageLookup

@[expose] public section

namespace SszX86.LinkedImage

/-- Unsigned half-open bounds on every row address; no ordering is assumed. -/
def InRange (rows : List Addressed) (lo hi : Nat) : Prop :=
  ∀ row ∈ rows, lo ≤ row.1.toBitVec.toNat ∧ row.1.toBitVec.toNat < hi

instance (rows : List Addressed) (lo hi : Nat) : Decidable (InRange rows lo hi) :=
  List.decidableBAll (fun row : Addressed =>
    lo ≤ row.1.toBitVec.toNat ∧ row.1.toBitVec.toNat < hi) rows

@[simp] theorem inRange_nil (lo hi : Nat) : InRange [] lo hi := by
  simp [InRange]

@[simp] theorem inRange_cons (row : Addressed) (rows : List Addressed) (lo hi : Nat) :
    InRange (row :: rows) lo hi ↔
      (lo ≤ row.1.toBitVec.toNat ∧ row.1.toBitVec.toNat < hi) ∧ InRange rows lo hi := by
  simp [InRange]

theorem inRange_append_iff (xs ys : List Addressed) (lo hi : Nat) :
    InRange (xs ++ ys) lo hi ↔ InRange xs lo hi ∧ InRange ys lo hi := by
  constructor
  · intro h
    exact ⟨fun row hr => h row (List.mem_append.mpr (Or.inl hr)),
      fun row hr => h row (List.mem_append.mpr (Or.inr hr))⟩
  · rintro ⟨hxs, hys⟩ row hr
    rcases List.mem_append.mp hr with hx | hy
    · exact hxs row hx
    · exact hys row hy

theorem inRange_mono {rows : List Addressed} {lo hi lo' hi' : Nat}
    (h : InRange rows lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    InRange rows lo' hi' := by
  intro row hr
  exact ⟨Nat.le_trans hlo (h row hr).1, Nat.lt_of_lt_of_le (h row hr).2 hhi⟩

/-- Adjacent chunk bounds compose without inspecting either chunk's rows. -/
theorem inRange_append {xs ys : List Addressed} {lo mid hi : Nat}
    (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (hxs : InRange xs lo mid) (hys : InRange ys mid hi) :
    InRange (xs ++ ys) lo hi := by
  exact (inRange_append_iff xs ys lo hi).mpr
    ⟨inRange_mono hxs (Nat.le_refl lo) hhi,
      inRange_mono hys hlo (Nat.le_refl hi)⟩

/-- Focus is valid even for unsorted middle rows and absent PCs. -/
theorem lookup_focus_range (before middle suffix : List Addressed) (pc : Int64)
    (lo hi : Nat)
    (hprefix : ∀ row ∈ before, row.1.toBitVec.toNat < lo)
    (hsuffix : ∀ row ∈ suffix, hi ≤ row.1.toBitVec.toNat)
    (hlo : lo ≤ pc.toBitVec.toNat) (hhi : pc.toBitVec.toNat < hi) :
    lookup (before ++ middle ++ suffix) pc = lookup middle pc := by
  apply lookup_focus
  · intro row hr heq
    have hlt := hprefix row hr
    rw [heq] at hlt
    exact Nat.not_lt_of_ge hlo hlt
  · intro row hr heq
    have hge := hsuffix row hr
    rw [heq] at hge
    exact Nat.not_lt_of_ge hge hhi

theorem lookup_focus_inRange (before middle suffix : List Addressed) (pc : Int64)
    (outerLo lo hi outerHi : Nat)
    (hprefix : InRange before outerLo lo) (hsuffix : InRange suffix hi outerHi)
    (hlo : lo ≤ pc.toBitVec.toNat) (hhi : pc.toBitVec.toNat < hi) :
    lookup (before ++ middle ++ suffix) pc = lookup middle pc :=
  lookup_focus_range before middle suffix pc lo hi
    (fun row hr => (hprefix row hr).2) (fun row hr => (hsuffix row hr).1) hlo hhi

/-- Transfer opaque addressed-row and range certificates to the real fetch. -/
theorem directivesAtAddress_focus (e : Executable)
    (before middle suffix : List Addressed) (pc : Int64) (outerLo lo hi outerHi : Nat)
    (hrows : e.withAddresses = before ++ middle ++ suffix)
    (hprefix : InRange before outerLo lo) (hsuffix : InRange suffix hi outerHi)
    (hlo : lo ≤ pc.toBitVec.toNat) (hhi : pc.toBitVec.toNat < hi) :
    e.directivesAtAddress pc = lookup middle pc := by
  rw [directivesAtAddress_eq_lookup, hrows]
  exact lookup_focus_inRange before middle suffix pc outerLo lo hi outerHi
    hprefix hsuffix hlo hhi

end SszX86.LinkedImage
