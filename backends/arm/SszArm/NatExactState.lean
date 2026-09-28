import SszArm.NatExactMemory

namespace SszArm.NatExact

/-- A store changes memory alone. Moving a register/PC update outside it lets
finite instruction cuts normalize once, before observing any state component. -/
theorem store_w (s : ArmState) (field : StateField) (value : state_value field)
    (bytes : Nat) (address : BitVec 64) (data : BitVec (bytes * 8)) :
    write_mem_bytes bytes address data (w field value s) =
      w field value (write_mem_bytes bytes address data s) := by
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]
  cases field <;>
    simp only [w, write_base_gpr, write_base_sfp, write_base_pc,
      write_base_flag, write_base_error]

/-- Keep the queried register symbolic: only this small algebraic lemma splits
on equality, never an instruction block multiplied by register case trees. -/
theorem r_gpr_w (s : ArmState) (query destination : BitVec 5) (value : BitVec 64) :
    r (.GPR query) (w (.GPR destination) value s) =
      if query = destination then value else r (.GPR query) s := by
  by_cases same : query = destination
  · subst query
    simp only [r_of_w_same, ↓reduceIte]
  · have different : StateField.GPR query ≠ StateField.GPR destination := by
      intro equal
      exact same (StateField.GPR.inj equal)
    simp only [r_of_w_different different, same, ↓reduceIte]

/-- A fixed orientation that hoists PC updates without rewrite cycles. -/
theorem gpr_w_pc (s : ArmState) (destination : BitVec 5) (value pc : BitVec 64) :
    w (.GPR destination) value (w .PC pc s) =
      w .PC pc (w (.GPR destination) value s) :=
  w_of_w_commute (by intro equal; cases equal)

end SszArm.NatExact
