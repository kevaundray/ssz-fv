import SszIndicesPaths
import SszIndicesDescriptorRefinement

set_option autoImplicit false

namespace SszNative.Indices

/-- A phase boundary exposes both the retained cursor and the entire ordered
trace, including the failed attempted operation. -/
theorem pathBind_success {α β : Type} (first : Outcome α) (value : α)
    (next : α → Nat → Outcome β) (success : first.result = .ok value) :
    bind first next =
      let second := next value first.used
      ⟨second.result, second.used, first.effects ++ second.effects⟩ := by
  simp only [bind, success]

theorem pathBind_failure {α β : Type} (first : Outcome α) (reason : Error)
    (next : α → Nat → Outcome β) (failure : first.result = .error reason) :
    bind first next = ⟨.error reason, first.used, first.effects⟩ := by
  simp only [bind, failure]

/-- Physical active-field lookup performs no allocation, even if the supplied
cursor/capacity are unusable. Its from_u128 attempt is still retained in the trace. -/
theorem activePosition_cursor (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : active.length < 2^64) :
    (activePosition active ordinal base capacity used).used = used := by
  by_cases fits : ordinal.value < 2^64
  · cases found : activeOrdinal active ordinal.value 0 with
    | none => simp [activePosition, ordinalToUsize_refines, fits, found, unchanged]
    | some position =>
        have bound := activeOrdinal_bound active ordinal.value 0 position found
        have small : position < 2^64 := by omega
        rw [activePosition_found active ordinal position base capacity used fits found small]
  · simp [activePosition, ordinalToUsize_refines, fits, unchanged]

theorem layoutPosition_cursor (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : active.length < 2^64) :
    (layoutPosition active ordinal base capacity used).used = used := by
  unfold layoutPosition bind
  cases result : (activePosition active ordinal base capacity used).result <;>
    simp only [unchanged] <;> exact activePosition_cursor active ordinal base capacity used physical

/-- Source fallback: multiplication failure prevents the ceiling shift entirely. -/
theorem chunkCount_vector_product_failure (element : Codec.Desc) (count : NatOperand)
    (base capacity used : Nat) (reason : NatArithmetic.Failure)
    (unpacked : packingShift (itemLength element) = none)
    (failure : (NatMul.run count (itemLength element) base capacity used).result = .error reason) :
    chunkCount (.vector element count) base capacity used =
      ⟨.error (.arithmetic reason),
        (NatMul.run count (itemLength element) base capacity used).used,
        [.arithmetic used (NatMul.run count (itemLength element) base capacity used)]⟩ := by
  simp only [chunkCount, unpacked, bind, arithmetic, failure, Except.mapError]

theorem chunkCount_vector_product_success (element : Codec.Desc) (count product : NatOperand)
    (base capacity used : Nat)
    (unpacked : packingShift (itemLength element) = none)
    (success : (NatMul.run count (itemLength element) base capacity used).result = .ok product) :
    chunkCount (.vector element count) base capacity used =
      let multiplied := NatMul.run count (itemLength element) base capacity used
      let shifted := ceilShift product 5 base capacity multiplied.used
      ⟨shifted.result, shifted.used, [.arithmetic used multiplied] ++ shifted.effects⟩ := by
  simp only [chunkCount, unpacked, bind, arithmetic, success, Except.mapError]

theorem chunkCount_list_same_resources (element : Codec.Desc) (count : NatOperand)
    (base capacity used : Nat) :
    chunkCount (.list element count) base capacity used =
      chunkCount (.vector element count) base capacity used := rfl

theorem unpackedPosition_product_failure (position width : NatOperand)
    (base capacity used : Nat) (reason : NatArithmetic.Failure)
    (failure : (NatMul.run position width base capacity used).result = .error reason) :
    unpackedPosition position width base capacity used =
      ⟨.error (.arithmetic reason), (NatMul.run position width base capacity used).used,
        [.arithmetic used (NatMul.run position width base capacity used)]⟩ := by
  simp only [unpackedPosition, bind, arithmetic, failure, Except.mapError]

/-- The product allocation survives failed quotient allocation; stop addition
has not occurred. The dividing event includes its complete initialized limbs. -/
theorem unpackedPosition_division_failure (position width product : NatOperand)
    (base capacity used : Nat) (reason : NatArithmetic.Failure)
    (multiplied : (NatMul.run position width base capacity used).result = .ok product)
    (failed : (NatDivision.run product 32 base capacity
      (NatMul.run position width base capacity used).used).result = .error reason) :
    unpackedPosition position width base capacity used =
      let first := NatMul.run position width base capacity used
      let second := NatDivision.run product 32 base capacity first.used
      ⟨.error (.arithmetic reason), second.used,
        [.arithmetic used first, .divide first.used second]⟩ := by
  simp only [unpackedPosition, bind, arithmetic, divide, multiplied, failed,
    Except.mapError, List.singleton_append]

/-- After successful multiplication and division, the final result and cursor
are exactly those of the stop addition, including on failure. There is no 32-byte
stop bound: raw oversized widths remain observable. -/
theorem unpackedPosition_addition_phase (position width product chunk : NatOperand)
    (remainder : BitVec 64) (base capacity used : Nat)
    (multiplied : (NatMul.run position width base capacity used).result = .ok product)
    (divided : (NatDivision.run product 32 base capacity
      (NatMul.run position width base capacity used).used).result = .ok (chunk, remainder)) :
    unpackedPosition position width base capacity used =
      let first := NatMul.run position width base capacity used
      let second := NatDivision.run product 32 base capacity first.used
      let third := NatAdd.run (.small remainder) width base capacity second.used
      ⟨(third.result.mapError Error.arithmetic).map
          (fun stop => ⟨chunk, .small remainder, stop⟩), third.used,
        [.arithmetic used first, .divide first.used second, .arithmetic second.used third]⟩ := by
  simp only [unpackedPosition, bind, arithmetic, divide, multiplied, divided,
    Except.mapError]
  cases added : (NatAdd.run (.small remainder) width base capacity
    (NatDivision.run product 32 base capacity
      (NatMul.run position width base capacity used).used).used).result <;>
    simp only [Except.map, unchanged, List.append_nil,
      List.singleton_append]

/-- Initial element lookup failure wins over the step kind, physical layout,
logical bound, and every arena operation. -/
theorem chunkPosition_element_failure (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (reason : Error)
    (failure : elementType shape step = .error reason) :
    chunkPosition shape step base capacity used = unchanged used (.error reason) := by
  simp only [chunkPosition, failure, bind, unchanged]

theorem chunkPosition_container (fields : List (String × Codec.Desc)) (ordinal : NatOperand)
    (child : Codec.Desc) (base capacity used : Nat)
    (found : fieldType fields ordinal = .ok child) :
    chunkPosition (.container fields) (.position ordinal) base capacity used =
      unchanged used (.ok ⟨ordinal, .small 0, itemLength child⟩) := by
  simp only [chunkPosition, elementType, found, bind_unchanged]

theorem chunkPosition_progressiveContainer (active : List Bool)
    (fields : List (String × Codec.Desc)) (ordinal : NatOperand) (child : Codec.Desc)
    (base capacity used : Nat) (found : fieldType fields ordinal = .ok child) :
    chunkPosition (.progressiveContainer active fields) (.position ordinal) base capacity used =
      bind (layoutPosition active ordinal base capacity used) fun position used =>
        unchanged used (.ok ⟨position, .small 0, itemLength child⟩) := by
  simp only [chunkPosition, elementType, found, bind_unchanged]

/-- Empty paths select the root on every raw declaration and every cursor,
without inspecting descriptor validity or reserving scratch. -/
theorem generalizedIndex_empty (shape : Codec.Desc) (base capacity used : Nat) :
    generalizedIndex shape [] base capacity used = unchanged used (.ok (.small 1)) := rfl

theorem resolveStep_bool (step : PathStep) (base capacity used : Nat) :
    resolveStep (.primitive .bool) step base capacity used =
      unchanged used (.error .noParts) := rfl

theorem resolveStep_uint (width : NatOperand) (step : PathStep) (base capacity used : Nat) :
    resolveStep (.primitive (.uint width)) step base capacity used =
      unchanged used (.error .noParts) := rfl

theorem generalizedIndex_step_failure (shape : Codec.Desc) (step : PathStep)
    (rest : List PathStep) (base capacity used : Nat) (reason : Error)
    (failed : (resolveStep shape step base capacity used).result = .error reason) :
    generalizedIndex shape (step :: rest) base capacity used =
      ⟨.error reason, (resolveStep shape step base capacity used).used,
        (resolveStep shape step base capacity used).effects⟩ := by
  simp only [generalizedIndex, bind, failed]

theorem generalizedIndex_terminal (shape : Codec.Desc) (step : PathStep)
    (index : NatOperand) (base capacity used : Nat)
    (resolved : (resolveStep shape step base capacity used).result = .ok (index, none)) :
    generalizedIndex shape [step] base capacity used =
      ⟨.ok index, (resolveStep shape step base capacity used).used,
        (resolveStep shape step base capacity used).effects⟩ := by
  simp only [generalizedIndex, bind, resolved, List.isEmpty_nil, ↓reduceIte,
    unchanged, List.append_nil]

theorem generalizedIndex_mixin_suffix (shape : Codec.Desc) (step next : PathStep)
    (rest : List PathStep) (index : NatOperand) (base capacity used : Nat)
    (resolved : (resolveStep shape step base capacity used).result = .ok (index, none)) :
    generalizedIndex shape (step :: next :: rest) base capacity used =
      ⟨.error .noPartsMixin, (resolveStep shape step base capacity used).used,
        (resolveStep shape step base capacity used).effects⟩ := by
  simp only [generalizedIndex, bind, resolved, List.isEmpty_cons, Bool.false_eq_true,
    ↓reduceIte, unchanged, List.append_nil]

/-- A deeper semantic or resource failure preserves all earlier relative-index
allocations, and performs no concat at the failing ancestor's unwind. -/
theorem generalizedIndex_child_failure (shape child : Codec.Desc) (step : PathStep)
    (rest : List PathStep) (index : NatOperand) (base capacity used : Nat) (reason : Error)
    (resolved : (resolveStep shape step base capacity used).result = .ok (index, some child))
    (failed : (generalizedIndex child rest base capacity
      (resolveStep shape step base capacity used).used).result = .error reason) :
    generalizedIndex shape (step :: rest) base capacity used =
      let first := resolveStep shape step base capacity used
      let second := generalizedIndex child rest base capacity first.used
      ⟨.error reason, second.used, first.effects ++ second.effects⟩ := by
  simp only [generalizedIndex, bind, resolved, failed]

/-- On unwind, concat starts at the child's final cursor. Its trace follows the
entire recursive descent/unwind trace, never an eager concatenation trace. -/
theorem generalizedIndex_unwind (shape child : Codec.Desc) (step : PathStep)
    (rest : List PathStep) (index inner : NatOperand) (base capacity used : Nat)
    (resolved : (resolveStep shape step base capacity used).result = .ok (index, some child))
    (recursed : (generalizedIndex child rest base capacity
      (resolveStep shape step base capacity used).used).result = .ok inner) :
    generalizedIndex shape (step :: rest) base capacity used =
      let first := resolveStep shape step base capacity used
      let second := generalizedIndex child rest base capacity first.used
      let third := concat index inner base capacity second.used
      ⟨third.result, third.used, first.effects ++ second.effects ++ third.effects⟩ := by
  simp only [generalizedIndex, bind, resolved, recursed, List.append_assoc]

/-- The initialized prefix belonging to the current step is never discarded,
regardless of whether recursion, a terminal check, or unwind later fails. -/
theorem generalizedIndex_retains_step (shape : Codec.Desc) (step : PathStep)
    (rest : List PathStep) (base capacity used : Nat) :
    ∃ suffix, (generalizedIndex shape (step :: rest) base capacity used).effects =
      (resolveStep shape step base capacity used).effects ++ suffix :=
  bind_retains_effects _ _

/-- A physical field count is converted without reserving scratch, while the
conversion attempt remains observable even at an exhausted arena cursor. -/
theorem chunkCount_container_physical (fields : List (String × Codec.Desc))
    (base capacity used : Nat) (physical : fields.length < 2^64) :
    chunkCount (.container fields) base capacity used =
      arithmetic used (NatArithmetic.unchanged used
        (.ok (.small (BitVec.ofNat 64 fields.length)))) := by
  simp only [chunkCount, fromWide_position fields.length base capacity used physical]

theorem chunkPosition_vector_out_of_range (element : Codec.Desc)
    (count position : NatOperand) (base capacity used : Nat)
    (outside : count.value ≤ position.value) :
    chunkPosition (.vector element count) (.position position) base capacity used =
      unchanged used (.error (.noSuchPosition position)) := by
  simp [chunkPosition, elementType, positionCount, bind_unchanged, outside]

theorem chunkPosition_list_out_of_range (element : Codec.Desc)
    (count position : NatOperand) (base capacity used : Nat)
    (outside : count.value ≤ position.value) :
    chunkPosition (.list element count) (.position position) base capacity used =
      unchanged used (.error (.noSuchPosition position)) := by
  simp [chunkPosition, elementType, positionCount, bind_unchanged, outside]

/-- The first matching selector is chosen without validation or scratch, even
when its value is huge, noncanonical, duplicated, or its child declaration invalid. -/
theorem resolvePosition_union_first (selector ordinal : NatOperand) (child : Codec.Desc)
    (rest : List (NatOperand × Codec.Desc)) (base capacity used : Nat)
    (same : selector.value = ordinal.value) :
    resolvePosition (.compatibleUnion ((selector, child) :: rest)) ordinal
      base capacity used = unchanged used (.ok (.small 2, some child)) := by
  simp only [resolvePosition, unionOption, nativeCmp_eq_iff, same, ↓reduceIte]

theorem resolvePosition_union_missing (variants : List (NatOperand × Codec.Desc))
    (ordinal : NatOperand) (base capacity used : Nat)
    (missing : unionOption variants ordinal = none) :
    resolvePosition (.compatibleUnion variants) ordinal base capacity used =
      unchanged used (.error (.noSuchOption ordinal)) := by
  simp only [resolvePosition, missing]

/-- Every completed prefix produced recursively is retained before any unwind
concat. This includes all child reservations and initialized limb lists, not just
the final returned operand. -/
theorem generalizedIndex_retains_child (shape child : Codec.Desc) (step : PathStep)
    (rest : List PathStep) (index : NatOperand) (base capacity used : Nat)
    (resolved : (resolveStep shape step base capacity used).result = .ok (index, some child)) :
    ∃ suffix, (generalizedIndex shape (step :: rest) base capacity used).effects =
      (resolveStep shape step base capacity used).effects ++
        (generalizedIndex child rest base capacity
          (resolveStep shape step base capacity used).used).effects ++ suffix := by
  obtain ⟨suffix, same⟩ := bind_retains_effects
    (generalizedIndex child rest base capacity (resolveStep shape step base capacity used).used)
    (fun inner used => concat index inner base capacity used)
  refine ⟨suffix, ?_⟩
  rw [generalizedIndex, pathBind_success _ (index, some child) _ resolved]
  change (resolveStep shape step base capacity used).effects ++
    (bind (generalizedIndex child rest base capacity
      (resolveStep shape step base capacity used).used)
      (fun inner used => concat index inner base capacity used)).effects = _
  rw [same, List.append_assoc]

end SszNative.Indices
