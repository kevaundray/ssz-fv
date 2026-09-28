import SszX86.MeasureBytesMemory
import SszX86.MeasureNoAlloc

namespace SszX86.Measure.Bytes
open SszNative SszNative.Serialize UintCodec

private theorem unchanged_of_noalloc (outcome : Outcome NatOperand) (used : Nat)
    (cursor : outcome.used = used) (calls : outcome.calls = []) :
    outcome = unchanged used outcome.result := by
  cases outcome
  simp_all [unchanged]

/-- The actual ByteVector destination529 reaches the real common epilogue3335.
All Value constructors and all represented widths are covered, including
arbitrary redundant high zeros, huge logical widths, and exact Scope payloads.
No arena allocation, successful expectedSize, or future ownership is assumed. -/
theorem vector_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.byteVector operand) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.byteVector operand) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.byteVector operand))) := by
  change Eventually (step e) _ (s, base + 529)
  apply eventually_trans (step e) _ _ _
    (vector_runs e base hc s operand value buffer address capacity used owned)
  intro t published
  apply Eventually.done
  refine ⟨published.1, ?_⟩
  have noalloc := vector_noalloc operand value (arenaState address capacity used)
  have model := unchanged_of_noalloc
    (measure (.byteVector operand) value (arenaState address capacity used))
    used.toNat noalloc.1 noalloc.2
  apply noalloc_body_post s t.1 (.byteVector operand) value buffer address capacity used
    _ owned model published.2.2.1 published.2.2.2
  · rw [published.2.1]
    exact vector_observed s operand value buffer address capacity used owned
  · rw [published.2.1, ← model]
    exact vector_memory_frame s operand value address capacity used

/-- The actual ByteList destination616 reaches3335 for every Value and every
logical cap. Limit retains the original operand pair and borrowed padding;
all publication, allocator, input, and activation frames are the shared BodyPost. -/
theorem list_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.byteList operand) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.byteList operand) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.byteList operand))) := by
  change Eventually (step e) _ (s, base + 616)
  apply eventually_trans (step e) _ _ _
    (list_runs e base hc s operand value buffer address capacity used owned)
  intro t published
  apply Eventually.done
  refine ⟨published.1, ?_⟩
  have noalloc := list_noalloc operand value (arenaState address capacity used)
  have model := unchanged_of_noalloc
    (measure (.byteList operand) value (arenaState address capacity used))
    used.toNat noalloc.1 noalloc.2
  apply noalloc_body_post s t.1 (.byteList operand) value buffer address capacity used
    _ owned model published.2.2.1 published.2.2.2
  · rw [published.2.1]
    exact list_observed s operand value buffer address capacity used owned
  · rw [published.2.1, ← model]
    exact list_memory_frame s operand value address capacity used owned.physical

end SszX86.Measure.Bytes
