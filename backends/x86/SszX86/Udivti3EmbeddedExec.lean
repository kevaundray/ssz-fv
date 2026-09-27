import SszX86.Udivti3Embedded
import SszX86.Udivti3Proofs

namespace SszX86.Udivti3.Embedded

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

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

private theorem layout_directive (image : Layout) (code : Program) (d : Directive × Nat)
    (h : d ∈ (image code).2) : d.1 ∈ code := by
  change d ∈ code.mapIdx (fun i v => (v, image.size i)) at h
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp h
  have he' := congrArg Prod.fst he
  rw [← he']
  exact List.getElem_mem hi

private theorem source_directive (base : Int64) (d : Directive × Nat)
    (h : d ∈ (Udivti3.executable base).2) : d.1 ∈ Udivti3.program :=
  layout_directive (Udivti3.layout base) Udivti3.program d h

private theorem directive_labels (a b : Labels)
    (ht : ∀ name ∈ usedLabels, a.label name = b.label name)
    (d : Directive) (hd : d ∈ Udivti3.program)
    (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    @Directive.interp a d s p next jmp = @Directive.interp b d s p next jmp := by
  have hdispatch := ht "udiv_dispatch" (by simp [usedLabels])
  have hhigh := ht "udiv_high" (by simp [usedLabels])
  have hword := ht "udiv_word_loop" (by simp [usedLabels])
  have hwordsub := ht "udiv_word_subtract" (by simp [usedLabels])
  have hwordnext := ht "udiv_word_next" (by simp [usedLabels])
  have hsecond := ht "udiv_second" (by simp [usedLabels])
  have hwide := ht "udiv_wide" (by simp [usedLabels])
  have hwideloop := ht "udiv_wide_loop" (by simp [usedLabels])
  have hwidesub := ht "udiv_wide_subtract" (by simp [usedLabels])
  have hwidenext := ht "udiv_wide_next" (by simp [usedLabels])
  have hone := ht "udiv_one" (by simp [usedLabels])
  have hzero := ht "udiv_zero" (by simp [usedLabels])
  simp only [Udivti3.program, List.mem_cons] at hd
  repeat' first | subst d | (rcases hd with hd | hd)
  all_goals first
  | rfl
  | simp only [Directive.interp, Instr.interp, Operation.interp,
      RelRegOrMem.interp, ConstExpr.interp,
      hdispatch, hhigh, hword, hwordsub, hwordnext, hsecond,
      hwide, hwideloop, hwidesub, hwidenext, hone, hzero]

private theorem directives_labels (base : Int64) (a b : Labels)
    (ht : ∀ name ∈ usedLabels, a.label name = b.label name)
    (ds : List (Directive × Nat)) (hd : ∀ d ∈ ds, d ∈ (Udivti3.executable base).2)
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

@[instance_reducible]
def layout (e : Executable) : Layout :=
  { start := e.1, size := fun i => (e.2[i]?.map Prod.snd).getD 0 }

abbrev step (e : Executable) := @step1 (layout e) e
/-- Agreement of actual steps wherever the standalone divider has code. -/
theorem step_eq (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineState) (post : MachineState → Prop)
    (hn : (Udivti3.executable base).directivesAtAddress s.2 ≠ []) :
    step e s post = Udivti3.step base s post := by
  unfold step Udivti3.step step1 Executable.step
  rw [hc.fetch s.2 hn]
  rw [directives_labels base e.labels (Udivti3.executable base).labels hc.targets
    _ (fun d hd => fetched_mem (Udivti3.executable base) s.2 d hd)]

/-- Empty standalone fetches are identity transitions and are erased rather
than assumed to agree with unrelated instructions in the containing image. -/
theorem eventually (e : Executable) (base : Int64) (hc : CodeAt e base)
    (post : MachineState → Prop) (s : MachineState)
    (h : Eventually (Udivti3.step base) post s) : Eventually (step e) post s := by
  induction h with
  | done s hs => exact .done s hs
  | step s mid hs _ ih =>
    by_cases hn : (Udivti3.executable base).directivesAtAddress s.2 = []
    · have hm : mid s := by
        simpa only [Udivti3.step, step1, Executable.step, hn, Directives.interp,
          Effects.All] using hs
      exact ih s hm
    · exact .step s mid ((step_eq e base hc s mid hn).symm ▸ hs) ih

/-- The already-proved divider's complete RET theorem in any structurally
containing executable. No execution-equivalence premise is exposed. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (hd : 0 < Udivti3.denominator s)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step e) (Udivti3.Returned s ra) (s, base) :=
  eventually e base hc _ _ (Udivti3.program_correct base s ra hd hr)
end SszX86.Udivti3.Embedded
