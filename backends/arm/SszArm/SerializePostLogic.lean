import SszArm.SerializeGeometry

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Error)

/-- A measurement error wins before either output guard, retaining all calls. -/
theorem outcome_of_measure_error (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (reason : Error) (failed : (measured s args desc value).result = .error reason) :
    outcome s args desc value =
      ⟨⟨.error reason, (measured s args desc value).used,
        (measured s args desc value).calls⟩, #[]⟩ := by
  change (SszNative.Serialize.measure desc value (arenaOf s args)).result = .error reason at failed
  simp only [outcome, SszNative.Serialize.serialize, SszNative.Serialize.encodedSize,
    SszNative.Serialize.bind, failed, measured]

/-- Host narrowing does not roll back retained measurement allocations. -/
theorem outcome_of_host_failure (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (operand : NatOperand) (success : (measured s args desc value).result = .ok operand)
    (tooLarge : ¬ operand.value < 2^64) :
    outcome s args desc value =
      ⟨⟨.error .outputTooSmall, (measured s args desc value).used,
        (measured s args desc value).calls⟩, #[]⟩ := by
  change (SszNative.Serialize.measure desc value (arenaOf s args)).result = .ok operand at success
  simp only [outcome, SszNative.Serialize.serialize, SszNative.Serialize.encodedSize,
    SszNative.Serialize.bind, success, SszNative.Serialize.hostSize, tooLarge,
    ↓reduceIte, SszNative.Serialize.unchanged, List.append_nil, measured]

/-- Capacity failure is later than host narrowing and retains the same cursor. -/
theorem outcome_of_capacity_failure (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (operand : NatOperand) (success : (measured s args desc value).result = .ok operand)
    (representable : operand.value < 2^64) (tooSmall : ¬ operand.value ≤ args.capacity.toNat) :
    outcome s args desc value =
      ⟨⟨.error .outputTooSmall, (measured s args desc value).used,
        (measured s args desc value).calls⟩, #[]⟩ := by
  change (SszNative.Serialize.measure desc value (arenaOf s args)).result = .ok operand at success
  simp only [outcome, SszNative.Serialize.serialize, SszNative.Serialize.encodedSize,
    SszNative.Serialize.bind, success, SszNative.Serialize.hostSize, representable,
    tooSmall, ↓reduceIte, SszNative.Serialize.unchanged, List.append_nil, measured]

/-- Successful emission contributes only output bytes, not new arena calls. -/
theorem outcome_of_success (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (operand : NatOperand) (success : (measured s args desc value).result = .ok operand)
    (representable : operand.value < 2^64) (fits : operand.value ≤ args.capacity.toNat) :
    outcome s args desc value =
      ⟨⟨.ok operand.value, (measured s args desc value).used,
        (measured s args desc value).calls⟩, SszNative.Serialize.emit desc value⟩ := by
  change (SszNative.Serialize.measure desc value (arenaOf s args)).result = .ok operand at success
  simp only [outcome, SszNative.Serialize.serialize, SszNative.Serialize.encodedSize,
    SszNative.Serialize.bind, success, SszNative.Serialize.hostSize, representable,
    fits, ↓reduceIte, SszNative.Serialize.unchanged, List.append_nil, measured]

theorem outcome_resources (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    (outcome s args desc value).outcome.used = (measured s args desc value).used ∧
      (outcome s args desc value).outcome.calls = (measured s args desc value).calls :=
  SszNative.Serialize.serialize_resources desc value args.capacity.toNat (arenaOf s args)

theorem expected_of_measured (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (physical : value.Physical) (operand : NatOperand)
    (success : (measured s args desc value).result = .ok operand) :
    SszNative.Serialize.expectedSize desc value = .ok operand.value := by
  have refinement := SszNative.Serialize.measure_refines desc value (arenaOf s args) physical
  change SszNative.Serialize.Measures (measured s args desc value).result _ at refinement
  rcases refinement with correct | exhausted
  · simp only [success, Except.map, SszNative.Serialize.eraseResult] at correct
    exact (Except.ok.inj correct).symm
  · rw [success] at exhausted
    cases exhausted

theorem outcome_writes_size_of_success (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (physical : value.Physical) (operand : NatOperand)
    (success : (measured s args desc value).result = .ok operand)
    (representable : operand.value < 2^64) (fits : operand.value ≤ args.capacity.toNat) :
    (outcome s args desc value).writes.size = operand.value := by
  have result : (outcome s args desc value).outcome.result = .ok operand.value := by
    rw [outcome_of_success s args desc value operand success representable fits]
  exact (SszNative.Serialize.serialize_success desc value args.capacity.toNat (arenaOf s args)
    physical operand.value result).2.1

theorem outcome_writes_size_le (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (physical : value.Physical) :
    (outcome s args desc value).writes.size ≤ args.capacity.toNat := by
  cases result : (outcome s args desc value).outcome.result with
  | ok count =>
    have exactSize := SszNative.Serialize.serialize_success desc value args.capacity.toNat
      (arenaOf s args) physical count result
    rw [show (outcome s args desc value).writes.size = count from exactSize.2.1]
    exact exactSize.2.2
  | error reason =>
    have empty := SszNative.Serialize.serialize_failure_writes desc value args.capacity.toNat
      (arenaOf s args) reason result
    change (outcome s args desc value).writes = #[] at empty
    simp only [empty, Array.size_empty, Nat.zero_le]

end SszArm.Serialize
