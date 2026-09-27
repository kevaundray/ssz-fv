import SszX86.Udivti3Impl

namespace SszX86.Udivti3.Embedded

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Exactly the label names occurring in the fixed divider image. -/
def usedLabels : List String :=
  ["udiv_dispatch", "udiv_high", "udiv_word_loop", "udiv_word_subtract",
   "udiv_word_next", "udiv_second", "udiv_wide", "udiv_wide_loop",
   "udiv_wide_subtract", "udiv_wide_next", "udiv_one", "udiv_zero"]

/-- A structural embedding, not a hypothesis about instruction execution.
The containing image may have arbitrary other labels and instructions. -/
structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ pc, (Udivti3.executable base).directivesAtAddress pc ≠ [] →
    e.directivesAtAddress pc = (Udivti3.executable base).directivesAtAddress pc
  targets : ∀ name ∈ usedLabels,
    e.labels.label name = (Udivti3.executable base).labels.label name

private theorem fetched_address (e : Executable) (pc : Int64)
    (h : e.directivesAtAddress pc ≠ []) :
    ∃ row ∈ e.withAddresses, row.1 = pc := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨row, hrow, _⟩ := List.mem_map.mp hd
  have hp := List.all_eq_true.mp (List.all_takeWhile
    (p := fun r : Int64 × Directive × Nat => decide (r.1 = pc))) row hrow
  have hdrop := (List.takeWhile_sublist _).subset hrow
  have hall := (List.dropWhile_sublist _).subset hdrop
  exact ⟨row, hall, by simpa using hp⟩

/-- Finite-row constructor used by linked-image binding witnesses. -/
theorem CodeAt.of_rows (e : Executable) (base : Int64)
    (hf : ∀ row ∈ (Udivti3.executable base).withAddresses,
      e.directivesAtAddress row.1 = (Udivti3.executable base).directivesAtAddress row.1)
    (ht : ∀ name ∈ usedLabels,
      e.labels.label name = (Udivti3.executable base).labels.label name) : CodeAt e base := by
  refine ⟨?_, ht⟩
  intro pc hn
  obtain ⟨row, hr, hpc⟩ := fetched_address (Udivti3.executable base) pc hn
  simpa only [hpc] using hf row hr



end SszX86.Udivti3.Embedded
