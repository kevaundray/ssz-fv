import SszArm.NatFromU128Proofs

namespace SszArm.NatFromU128

open UintCodec (widthLoad)

/-- The native Small branch performs no reservation regardless of cursor or capacity. -/
theorem small_resources (s : ArmState) (small : r (.GPR 3#5) s = 0#64) :
    (outcome s).allocation = none ∧ (outcome s).written = [] ∧
      (outcome s).used = (usedWord s).toNat := by
  rw [outcome_small s small]
  exact ⟨rfl, rfl, rfl⟩

theorem allocated_iff (s : ArmState) (reservation : SszNative.Arena.Reservation) :
    (outcome s).allocation = some reservation ↔
      r (.GPR 3#5) s ≠ 0#64 ∧
      SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat
        (usedWord s).toNat 2 = some reservation := by
  by_cases small : r (.GPR 3#5) s = 0#64
  · simp [outcome_small s small, SszNative.NatArithmetic.unchanged, small]
  · have notSmall : ¬ (wide s).toNat < 2^64 := fun h => small ((wide_small s).1 h)
    cases reserved : SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2 <;>
      simp [outcome, SszNative.NatArithmetic.fromWide, notSmall, reserved,
        SszNative.NatArithmetic.unchanged, SszNative.NatArithmetic.committed, small]

/-- Failure is exactly the complement of the five native guards, never a
logical capacity ceiling or an assumed inability to obtain scratch. -/
theorem exhausted_iff (s : ArmState) :
    (outcome s).result = .error .scratchExhausted ↔
      r (.GPR 3#5) s ≠ 0#64 ∧
      ¬ SszNative.Arena.Checks (addressWord s).toNat (capacityWord s).toNat (usedWord s).toNat 2 := by
  by_cases small : r (.GPR 3#5) s = 0#64
  · simp [outcome_small s small, SszNative.NatArithmetic.unchanged, small]
  · have notSmall : ¬ (wide s).toNat < 2^64 := fun h => small ((wide_small s).1 h)
    rw [← SszNative.Arena.reserve_eq_none_iff_checks _ _ _ 2 (by decide)]
    cases reserved : SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2 <;>
      simp [outcome, SszNative.NatArithmetic.fromWide, notSmall, reserved,
        SszNative.NatArithmetic.unchanged, SszNative.NatArithmetic.committed, small]

/-- Both original full words are physically present after allocation, with the
exact aligned pointer and committed cursor, including a zero low word. -/
theorem Post.allocated {s t : ArmState} (post : Post s t)
    (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome s).allocation = some reservation) :
    reservation.pointer = SszNative.Arena.aligned ((addressWord s).toNat + (usedWord s).toNat) ∧
    reservation.used = SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2 ∧
    reservation.pointer % 8 = 0 ∧
    (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = reservation.used ∧
    (SszNative.NatOperand.large (BitVec.ofNat 64 reservation.pointer)
      [r (.GPR 2#5) s, r (.GPR 3#5) s]).At (widthLoad t) := by
  obtain ⟨large, reserved⟩ := (allocated_iff s reservation).1 allocated
  obtain ⟨checks, shape⟩ := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2
    (by decide) reservation).1 reserved
  have model := outcome_wide s large checks
  have stored := post.written reservation allocated
  rw [model] at stored
  have cursor := post.cursor
  rw [model] at cursor
  subst reservation
  exact ⟨SszNative.Arena.start_pointer _ _, rfl,
    by rw [SszNative.Arena.start_pointer]; exact SszNative.Arena.aligned_mod _,
    cursor, stored⟩

/-- Neither Small nor an exhausted wide construction changes the original cursor. -/
theorem Post.unallocated {s t : ArmState} (post : Post s t)
    (unallocated : (outcome s).allocation = none) :
    (outcome s).written = [] ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t = usedWord s := by
  by_cases small : r (.GPR 3#5) s = 0#64
  · have model := outcome_small s small
    constructor
    · rw [model]; rfl
    · apply BitVec.eq_of_toNat_eq
      simpa only [model, SszNative.NatArithmetic.unchanged] using post.cursor
  · cases reserved : SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2 with
    | none =>
      have model := outcome_failure s small reserved
      constructor
      · rw [model]; rfl
      · apply BitVec.eq_of_toNat_eq
        simpa only [model, SszNative.NatArithmetic.unchanged] using post.cursor
    | some reservation =>
      have allocated := (allocated_iff s reservation).2 ⟨small, reserved⟩
      rw [unallocated] at allocated
      contradiction

/-- Value refinement is exported from physical entry rather than a future
callee state: execution, ABI, resource and exact two-limb facts are retained. -/
theorem correct_value (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s) :
    ∃ fuel t, run fuel s = t ∧ Post s t ∧
      ∀ result, (outcome s).result = .ok result →
        SszNative.NatMemory.Pair (widthLoad t) result.pointer result.payload (wide s).toNat := by
  obtain ⟨fuel, t, runs, post⟩ := correct s base hc he ha hp owned
  exact ⟨fuel, t, runs, post, fun result success => post.pair result success⟩

end SszArm.NatFromU128
