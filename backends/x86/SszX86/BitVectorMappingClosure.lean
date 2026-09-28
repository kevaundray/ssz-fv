import SszX86.BitVectorMappingExec

namespace SszX86.BitVector.Mapping

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem avx_load_lift (s : MachineData) (address : BitVec 64) (w : AvxWidth)
    (ret : w.type → MachineData → Effects) (aligned : Bool) (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (s.loadAvx address w ret aligned).All P → (s.loadAvx address w ret aligned).All Q := by
  unfold MachineData.loadAvx
  split
  · exact id
  · cases read : Mem.loadInt s.dmem address w.bytes <;> simp only [Effects.All]
    · exact False.elim
    · exact hret _

theorem avx_store_lift (s : MachineData) (address : BitVec 64) {w : AvxWidth}
    (value : w.type) (ret : MachineData → Effects) (aligned : Bool) (P Q : MachineState → Prop)
    (hret : (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All P →
      (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All Q) :
    (s.storeAvx address value ret aligned).All P → (s.storeAvx address value ret aligned).All Q := by
  unfold MachineData.storeAvx
  split
  · exact id
  · cases read : Mem.loadInt s.dmem address w.bytes <;> simp only [Effects.All]
    · exact False.elim
    · exact hret

theorem avx_regmem_lift [Labels] [AddressSize] {w : AvxWidth} (o : AvxRegOrMem w)
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (aligned : Bool) (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (o.interp s p ret aligned).All P → (o.interp s p ret aligned).All Q := by
  cases o with
  | avx r => exact hret _
  | mem a => exact avx_load_lift s _ w ret aligned P Q hret

theorem avx_operand_lift [Labels] [AddressSize] {w : AvxWidth} (o : AvxOperand w)
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (aligned : Bool) (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (o.interp s p ret aligned).All P → (o.interp s p ret aligned).All Q := by
  cases o with
  | regOrMem rm => exact avx_regmem_lift rm s p ret aligned P Q hret

theorem avx_set_lift [Labels] [AddressSize] {w : AvxWidth} (dst : AvxDst w)
    (s : MachineData) (p : Std.Rco Int64) (value : w.type)
    (ret : MachineData → Effects) (aligned : Bool) (P Q : MachineState → Prop)
    (before : DataMem) (hdom : Extends before s.dmem)
    (hret : ∀ t, Extends before t.dmem → (ret t).All P → (ret t).All Q) :
    (s.setAvx dst value p ret aligned).All P → (s.setAvx dst value p ret aligned).All Q := by
  cases dst with
  | avx r => exact hret _ hdom
  | mem a =>
    apply avx_store_lift
    exact hret _ (hdom.trans (Extends.store _ _ _ _))

theorem avx_legacy_set_lift [Labels] [AddressSize] {w : AvxWidth} (dst : AvxDst w)
    (s : MachineData) (p : Std.Rco Int64) (value : w.type)
    (ret : MachineData → Effects) (aligned : Bool) (P Q : MachineState → Prop)
    (before : DataMem) (hdom : Extends before s.dmem)
    (hret : ∀ t, Extends before t.dmem → (ret t).All P → (ret t).All Q) :
    (s.setAvxLegacy dst value p ret aligned).All P →
      (s.setAvxLegacy dst value p ret aligned).All Q := by
  cases dst with
  | avx r => exact hret _ hdom
  | mem a =>
    apply avx_store_lift
    exact hret _ (hdom.trans (Extends.store _ _ _ _))

theorem avx_operation_lift [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w)
    (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects)
    (P Q : MachineState → Prop) (before : DataMem) (hdom : Extends before s.dmem)
    (hnext : ∀ t, Extends before t.dmem → (next t).All P → (next t).All Q) :
    (op.interp p s next).All P → (op.interp p s next).All Q := by
  cases op <;> simp only [AvxOperation.interp]
  all_goals
    repeat' first
    | (apply hnext; assumption)
    | (apply avx_operand_lift; intro value)
    | (apply avx_regmem_lift; intro value)
    | (apply avx_set_lift (before := before) <;> first | assumption | (intro t ht))
    | (apply avx_legacy_set_lift (before := before) <;> first | assumption | (intro t ht))

theorem instruction_lift [Labels] (instruction : Instr)
    (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) (P Q : MachineState → Prop)
    (before : DataMem) (hdom : Extends before s.dmem)
    (hnext : ∀ t, Extends before t.dmem → (next t).All P → (next t).All Q)
    (hjump : ∀ pc t, Extends before t.dmem → (jump pc t).All P → (jump pc t).All Q) :
    (instruction.interp s p next jump).All P → (instruction.interp s p next jump).All Q := by
  cases instruction with
  | regular addressWidth operandWidth op =>
    exact @operation_lift _ ⟨addressWidth⟩ operandWidth op s p next jump P Q before hdom hnext hjump
  | avx addressWidth operandWidth op =>
    exact @avx_operation_lift _ ⟨addressWidth⟩ operandWidth op s p next P Q before hdom hnext

theorem directive_lift [Labels] (directive : Directive)
    (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) (P Q : MachineState → Prop)
    (before : DataMem) (hdom : Extends before s.dmem)
    (hnext : ∀ t, Extends before t.dmem → (next t).All P → (next t).All Q)
    (hjump : ∀ pc t, Extends before t.dmem → (jump pc t).All P → (jump pc t).All Q) :
    (directive.interp s p next jump).All P → (directive.interp s p next jump).All Q := by
  cases directive with
  | label name => exact hnext s hdom
  | instr instruction => exact instruction_lift instruction s p next jump P Q before hdom hnext hjump
  | byteArray data => exact False.elim

theorem directives_lift [Labels] (directives : List (Directive × Nat))
    (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects)
    (P Q : MachineState → Prop) (before : DataMem) (hdom : Extends before s.dmem)
    (hret : ∀ pc t, Extends before t.dmem → (ret pc t).All P → (ret pc t).All Q) :
    (Directives.interp directives s pc ret).All P → (Directives.interp directives s pc ret).All Q := by
  induction directives generalizing s pc with
  | nil => exact hret pc s hdom
  | cons row rest ih =>
    apply directive_lift row.1 s _ _ ret P Q before hdom
    · intro t ht
      exact ih t _ ht
    · exact hret

/-- Every safe actual step retains all incoming memory mappings, including bytes
inside a callee's coarse write frame that its semantic Post leaves unspecified. -/
theorem step_extends (e : Executable) (s : MachineState) (P : MachineState → Prop)
    (h : step e s P) :
    step e s (fun t => P t ∧ Extends s.1.dmem t.1.dmem) := by
  letI := e.labels
  apply directives_lift (e.directivesAtAddress s.2) s.1 s.2
    (fun pc t => Effects.done (t, pc)) P _ s.1.dmem (Extends.refl _) _ h
  intro pc t ht hp
  exact ⟨hp, ht⟩

/-- Strengthening a proved execution uses the actual transition proof at every
step; it does not assume a stronger callee postcondition. -/
theorem eventually_extends (e : Executable) (P : MachineState → Prop) (s : MachineState)
    (execution : Eventually (step e) P s) :
    ∀ before, Extends before s.1.dmem →
      Eventually (step e) (fun t => P t ∧ Extends before t.1.dmem) s := by
  induction execution with
  | done initial hp =>
    intro before hdom
    exact .done initial ⟨hp, hdom⟩
  | step initial intermediate hstep continuation ih =>
    intro before hdom
    refine .step initial (fun t => intermediate t ∧ Extends initial.1.dmem t.1.dmem)
      (step_extends e initial intermediate hstep) ?_
    intro t ht
    exact ih t ht.1 before (hdom.trans ht.2)

theorem retains_mapping (e : Executable) (P : MachineState → Prop) (s : MachineState)
    (execution : Eventually (step e) P s) :
    Eventually (step e) (fun t => P t ∧ Extends s.1.dmem t.1.dmem) s :=
  eventually_extends e P s execution s.1.dmem (Extends.refl _)

end SszX86.BitVector.Mapping
