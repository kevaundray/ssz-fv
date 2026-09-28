import SszX86.NatMulCore
import SszX86.MemsetProofs

namespace SszX86.NatMul.MemsetCall

/-- Only labels present in the pinned, accepted memset image. -/
def memsetLabels : List String := ["bulk27", "tail44", "byte49", "done62"]

/-- Structural linked-code ownership; it makes no execution assumption. -/
structure MemsetCodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ pc, (memsetExecutable base).directivesAtAddress pc ≠ [] →
    e.directivesAtAddress pc = (memsetExecutable base).directivesAtAddress pc
  targets : ∀ name ∈ memsetLabels,
    e.labels.label name = (memsetExecutable base).labels.label name

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

theorem MemsetCodeAt.of_rows (e : Executable) (base : Int64)
    (hf : ∀ row ∈ (memsetExecutable base).withAddresses,
      e.directivesAtAddress row.1 = (memsetExecutable base).directivesAtAddress row.1)
    (ht : ∀ name ∈ memsetLabels,
      e.labels.label name = (memsetExecutable base).labels.label name) :
    MemsetCodeAt e base := by
  refine ⟨?_, ht⟩
  intro pc hn
  obtain ⟨row, hr, hpc⟩ := fetched_address (memsetExecutable base) pc hn
  simpa only [hpc] using hf row hr

private theorem fetched_mem (e : Executable) (pc : Int64) (d : Directive × Nat)
    (h : d ∈ e.directivesAtAddress pc) : d ∈ e.2 := by
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp h
  have hdrop := (List.takeWhile_sublist _).subset hrow
  have hall := (List.dropWhile_sublist _).subset hdrop
  have hm : row.2 ∈ e.withAddresses.map Prod.snd := List.mem_map.mpr ⟨row, hall, rfl⟩
  have same : e.withAddresses.map Prod.snd = e.2 := by
    cases e with
    | mk address rows => exact Kraken.Executable.withAddresses_map_snd rows address
  simpa only [same] using hm

private theorem layout_directive (image : Layout) (imageCode : Program) (d : Directive × Nat)
    (h : d ∈ (image imageCode).2) : d.1 ∈ imageCode := by
  change d ∈ imageCode.mapIdx (fun i v => (v, image.size i)) at h
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp h
  have he' := congrArg Prod.fst he
  rw [← he']
  exact List.getElem_mem hi

private theorem source_directive (base : Int64) (d : Directive × Nat)
    (h : d ∈ (memsetExecutable base).2) : d.1 ∈ memsetProgram :=
  layout_directive (memsetLayout base) memsetProgram d h

private theorem directive_labels (a b : Labels)
    (ht : ∀ name ∈ memsetLabels, a.label name = b.label name)
    (d : Directive) (hd : d ∈ memsetProgram)
    (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    @Directive.interp a d s p next jmp = @Directive.interp b d s p next jmp := by
  have hbulk := ht "bulk27" (by simp [memsetLabels])
  have htail := ht "tail44" (by simp [memsetLabels])
  have hbyte := ht "byte49" (by simp [memsetLabels])
  have hdone := ht "done62" (by simp [memsetLabels])
  simp only [memsetProgram, List.mem_cons] at hd
  repeat' first | subst d | (rcases hd with hd | hd)
  all_goals first
  | rfl
  | simp only [Directive.interp, Instr.interp, Operation.interp,
      hbulk, htail, hbyte, hdone]

private theorem directives_labels (base : Int64) (a b : Labels)
    (ht : ∀ name ∈ memsetLabels, a.label name = b.label name)
    (ds : List (Directive × Nat)) (hd : ∀ d ∈ ds, d ∈ (memsetExecutable base).2)
    (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects) :
    @Directives.interp a ds s pc ret = @Directives.interp b ds s pc ret := by
  induction ds generalizing s pc with
  | nil => rfl
  | cons d ds ih =>
    simp only [Directives.interp]
    rw [directive_labels a b ht d.1 (source_directive base d (hd d (by simp)))]
    congr 1
    funext t
    exact ih (fun v hv => hd v (List.mem_cons_of_mem _ hv)) t _

theorem memset_step_eq (e : Executable) (base : Int64) (hc : MemsetCodeAt e base)
    (s : MachineState) (post : MachineState → Prop)
    (hn : (memsetExecutable base).directivesAtAddress s.2 ≠ []) :
    step e s post = memsetStep base s post := by
  unfold step memsetStep step1 Executable.step
  rw [hc.fetch s.2 hn]
  rw [directives_labels base e.labels (memsetExecutable base).labels hc.targets
    _ (fun d hd => fetched_mem (memsetExecutable base) s.2 d hd)]

/-- Transport the accepted helper theorem into the real containing executable. -/
theorem memset_eventually (e : Executable) (base : Int64) (hc : MemsetCodeAt e base)
    (post : MachineState → Prop) (s : MachineState)
    (h : Eventually (memsetStep base) post s) : Eventually (step e) post s := by
  induction h with
  | done s hs => exact .done s hs
  | step s mid hs _ ih =>
    by_cases hn : (memsetExecutable base).directivesAtAddress s.2 = []
    · have hm : mid s := by
        simpa only [memsetStep, step1, Executable.step, hn, Directives.interp,
          Effects.All] using hs
      exact ih s hm
    · exact .step s mid ((memset_step_eq e base hc s mid hn).symm ▸ hs) ih

end SszX86.NatMul.MemsetCall
