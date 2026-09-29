import SszProofMulti
import SszIndicesFrontierResources

set_option autoImplicit false

namespace SszNative.Proof

/-- Successful Nat-array reservation bounds helper count independently of arena
validity. This justifies lossless u128 count-error operands, not a logical cap. -/
theorem multiHelper_count_physical (indices : List NatOperand) (arena : Delimited.ArenaState)
    (helpers : Indices.NatSlice)
    (success : (Indices.helperIndices indices arena.base arena.capacity arena.used).result =
      .ok helpers) : helpers.values.length < 2^64 := by
  obtain ⟨count, reserved, length, completed⟩ :=
    (Indices.helperIndices_resources indices arena.base arena.capacity arena.used).success helpers success
  rw [length]
  unfold TypedArena.reserve at reserved
  split at reserved
  · rename_i empty
    have zero : count = 0 := by simpa [Indices.natLayout] using empty
    rw [zero]
    decide
  · split at reserved
    · rename_i checked
      have byteBound := checked.1
      change 16 * count < 2^63 at byteBound
      have wider : 2^63 < 2^64 := by decide
      omega
    · cases reserved

end SszNative.Proof
