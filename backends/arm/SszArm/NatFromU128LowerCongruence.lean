import SszArm.NatFromU128LowerBase

namespace SszArm.NatFromU128

/-- Moving a register update outside a store erases irrelevant state structure
before the proved scratch read equations are applied. -/
theorem store_field_write (s : ArmState) (field : StateField) (value : state_value field)
    (bytes : Nat) (address : BitVec 64) (word : BitVec (bytes * 8)) :
    write_mem_bytes bytes address word (w field value s) =
      w field value (write_mem_bytes bytes address word s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    by_cases equal : f = field
    · subst f; simp only [state_simp_rules]
    · simp only [r_of_write_mem_bytes, r_of_w_different equal]
  · simp only [state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simpa only [ArmState.mem_w_eq_mem] using
      mem_write_mem_bytes_of_mem_eq
        (show (w field value s).mem = s.mem by simp only [ArmState.mem_w_eq_mem])
        bytes address word

end SszArm.NatFromU128
