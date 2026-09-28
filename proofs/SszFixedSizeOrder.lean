import SszFixedSizeResources

namespace SszNative.FixedSize

open Serialize (Outcome unchanged)

/-- The trace drops only the remainder, never any scratch effect. -/
theorem divisionCall_exact (call : NatArithmetic.Outcome (NatOperand × BitVec 64)) :
    (divisionCall call).result = call.result.map Prod.fst ∧
      (divisionCall call).used = call.used ∧
      (divisionCall call).allocation = call.allocation ∧
      (divisionCall call).written = call.written := ⟨rfl, rfl, rfl, rfl⟩

theorem bitWidth_division_error (length : NatOperand) (arena : Delimited.ArenaState)
    (reason : Serialize.Error) (failed : (div8 length arena).result = .error reason) :
    bitWidth length arena =
      ⟨.error reason, (div8 length arena).used, (div8 length arena).calls⟩ :=
  bind_error _ _ reason failed

/-- A zero remainder skips the increment call and returns the exact quotient. -/
theorem bitWidth_exact (length quotient : NatOperand) (arena : Delimited.ArenaState)
    (divided : (div8 length arena).result = .ok (quotient, 0)) :
    bitWidth length arena =
      ⟨.ok quotient, (div8 length arena).used, (div8 length arena).calls⟩ := by
  simp only [bitWidth, Serialize.bind, divided, ↓reduceIte, unchanged, List.append_nil]

/-- The increment uses the division's committed cursor. Its failure is retained
as the second call, while every quotient allocation and write remains visible. -/
theorem bitWidth_rounded (length quotient : NatOperand) (remainder : BitVec 64)
    (arena : Delimited.ArenaState)
    (divided : (div8 length arena).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) :
    bitWidth length arena =
      let next := add quotient (.small 1) { arena with used := (div8 length arena).used }
      ⟨next.result, next.used, (div8 length arena).calls ++ next.calls⟩ := by
  simp only [bitWidth, Serialize.bind, divided, nonzero, ↓reduceIte]

/-- In raw measurement a variable child retains its preceding effects. Vector
length zero does not bypass child measurement or classification. -/
theorem measureFixed_vector_none (element : Codec.Desc) (length : NatOperand)
    (arena : Delimited.ArenaState) (notFixed : (measureFixed element arena).result = .ok none) :
    measureFixed (.vector element length) arena =
      ⟨.ok none, (measureFixed element arena).used, (measureFixed element arena).calls⟩ := by
  simp only [measureFixed, Serialize.bind, notFixed, unchanged, List.append_nil]

theorem measureFixed_vector_step (element : Codec.Desc) (length width : NatOperand)
    (arena : Delimited.ArenaState)
    (measured : (measureFixed element arena).result = .ok (some width)) :
    measureFixed (.vector element length) arena =
      let product := mul width length { arena with used := (measureFixed element arena).used }
      ⟨product.result.map some, product.used,
        (measureFixed element arena).calls ++ product.calls⟩ := by
  simp only [measureFixed, Serialize.bind, measured]
  cases product : (mul width length { arena with used := (measureFixed element arena).used }).result <;>
    simp only [Except.map, unchanged, List.append_nil]

theorem measureFields_child_none (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) (total : NatOperand) (arena : Delimited.ArenaState)
    (notFixed : (measureFixed field arena).result = .ok none) :
    measureFields ((name, field) :: rest) total arena =
      ⟨.ok none, (measureFixed field arena).used, (measureFixed field arena).calls⟩ := by
  simp only [measureFields, Serialize.bind, notFixed, unchanged, List.append_nil]

theorem measureFields_child_error (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) (total : NatOperand) (arena : Delimited.ArenaState)
    (reason : Serialize.Error) (failed : (measureFixed field arena).result = .error reason) :
    measureFields ((name, field) :: rest) total arena =
      ⟨.error reason, (measureFixed field arena).used, (measureFixed field arena).calls⟩ := by
  simp only [measureFields, Serialize.bind, failed]

/-- Each successful field and running-total addition precedes the recursive
suffix. This equation also covers a suffix returning None or failing. -/
theorem measureFields_step (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) (total width next : NatOperand)
    (arena : Delimited.ArenaState)
    (measured : (measureFixed field arena).result = .ok (some width))
    (added : (add total width { arena with used := (measureFixed field arena).used }).result = .ok next) :
    measureFields ((name, field) :: rest) total arena =
      let child := measureFixed field arena
      let sum := add total width { arena with used := child.used }
      let remaining := measureFields rest next { arena with used := sum.used }
      ⟨remaining.result, remaining.used, child.calls ++ sum.calls ++ remaining.calls⟩ := by
  simp only [measureFields, Serialize.bind, measured, added, List.append_assoc]

/-- A failed addition makes no reservation of its own, but does not reset the
cursor or trace committed while measuring this field (or preceding fields). -/
theorem measureFields_add_error (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) (total width : NatOperand)
    (arena : Delimited.ArenaState) (reason : NatArithmetic.Failure)
    (measured : (measureFixed field arena).result = .ok (some width))
    (failed : (NatAdd.run total width arena.base arena.capacity
      (measureFixed field arena).used).result = .error reason) :
    measureFields ((name, field) :: rest) total arena =
      ⟨.error (.arithmetic reason), (measureFixed field arena).used,
        (measureFixed field arena).calls ++
          [NatArithmetic.unchanged (measureFixed field arena).used (.error reason)]⟩ := by
  have same := NatAdd.failure_unchanged total width arena.base arena.capacity
    (measureFixed field arena).used reason failed
  simp only [measureFields, Serialize.bind, measured, add, arithmetic, same,
    NatArithmetic.unchanged, Except.mapError]

/-- Multiplication failure likewise retains the measured child's allocations. -/
theorem measureFixed_mul_error (element : Codec.Desc) (length width : NatOperand)
    (arena : Delimited.ArenaState) (reason : NatArithmetic.Failure)
    (measured : (measureFixed element arena).result = .ok (some width))
    (failed : (NatMul.run width length arena.base arena.capacity
      (measureFixed element arena).used).result = .error reason) :
    measureFixed (.vector element length) arena =
      ⟨.error (.arithmetic reason), (measureFixed element arena).used,
        (measureFixed element arena).calls ++
          [NatArithmetic.unchanged (measureFixed element arena).used (.error reason)]⟩ := by
  have same := NatMul.failure_unchanged width length arena.base arena.capacity
    (measureFixed element arena).used reason failed
  simp only [measureFixed, Serialize.bind, measured, mul, arithmetic, same,
    NatArithmetic.unchanged, Except.mapError]

end SszNative.FixedSize
