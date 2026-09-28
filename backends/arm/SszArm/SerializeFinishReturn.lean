import SszArm.SerializeExec
import SszArm.DelimitedMemory
import SszArm.EmitContract

namespace SszArm.Serialize.Finish

open Delimited (MemoryFrame Protected)

abbrev sp (s : ArmState) : BitVec 64 := r (.GPR 31#5) s
abbrev result (s : ArmState) : BitVec 64 := r (.GPR 19#5) s

def saved : List (BitVec 5 × Nat) :=
  [(30#5, 96), (23#5, 104), (22#5, 112), (21#5, 120), (20#5, 128), (19#5, 136)]

inductive Exit where
  | measurement | capacity | emitted
  deriving DecidableEq

def Exit.entry : Exit → Nat
  | .measurement => 116
  | .capacity => 628
  | .emitted => 672

def Exit.ops : Exit → List Op
  | .measurement => [.p116, .p120, .p124, .p128, .p132]
  | .capacity => [.p628, .p632, .p636, .p640, .p644]
  | .emitted => [.p672, .p676, .p680, .p684, .p688]

/-- The original epilogue reads the saved activation, not current x19--x23/LR. -/
def returned (s : ArmState) : ArmState :=
  w .PC (read_mem_bytes 8 (sp s + 96#64) s)
  (w (.GPR 31#5) (sp s + 144#64)
  (w (.GPR 23#5) (read_mem_bytes 8 (sp s + 104#64) s)
  (w (.GPR 30#5) (read_mem_bytes 8 (sp s + 96#64) s)
  (w (.GPR 21#5) (read_mem_bytes 8 (sp s + 120#64) s)
  (w (.GPR 22#5) (read_mem_bytes 8 (sp s + 112#64) s)
  (w (.GPR 19#5) (read_mem_bytes 8 (sp s + 136#64) s)
  (w (.GPR 20#5) (read_mem_bytes 8 (sp s + 128#64) s) s)))))))

theorem return_effect (kind : Exit) (base : BitVec 64) (s : ArmState) :
    block base kind.ops s = returned s := by
  cases kind <;>
    simp [Exit.ops, block, Op.effect, next, put, returned, sp, state_simp_rules,
      BitVec.add_assoc]
  all_goals
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field <;> simp [state_simp_rules, w, write_base_gpr, write_base_pc]
    · simp [state_simp_rules]
    · intro bytes address
      simp [state_simp_rules]

theorem return_run (kind : Exit) (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    run 5 s = returned s := by
  have follows : Follows base kind.ops s := by
    change r .PC s = _ at pc
    cases kind <;>
      simp only [Exit.entry] at pc <;>
      simp [Follows, Exit.ops, Op.row, Op.effect, next, put,
        state_simp_rules, BitVec.add_assoc, pc]
  have execution := block_run base kind.ops s code error aligned follows
  rw [return_effect] at execution
  cases kind <;> exact execution

@[simp] theorem returned_memory (s : ArmState) : (returned s).mem = s.mem := by
  simp [returned, state_simp_rules]

@[simp] theorem returned_program (s : ArmState) : (returned s).program = s.program := by
  simp [returned, state_simp_rules]

@[simp] theorem returned_error (s : ArmState) : read_err (returned s) = read_err s := by
  simp [returned, state_simp_rules]

@[simp] theorem returned_pc (s : ArmState) :
    read_pc (returned s) = read_mem_bytes 8 (sp s + 96#64) s := by
  simp [returned, state_simp_rules]

@[simp] theorem returned_sp (s : ArmState) : sp (returned s) = sp s + 144#64 := by
  simp [returned, sp, state_simp_rules]

theorem returned_saved (s : ArmState) (reg : BitVec 5) (displacement : Nat)
    (member : (reg, displacement) ∈ saved) :
    r (.GPR reg) (returned s) = read_mem_bytes 8 (sp s + BitVec.ofNat 64 displacement) s := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [returned, state_simp_rules]

theorem saved_bounds (reg : BitVec 5) (displacement : Nat)
    (member : (reg, displacement) ∈ saved) :
    96 ≤ displacement ∧ displacement + 8 ≤ 144 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem returned_other (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5, 31#5]) :
    r (.GPR reg) (returned s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  simp [returned, state_simp_rules, untouched.1, untouched.2.1,
    untouched.2.2.1, untouched.2.2.2.1, untouched.2.2.2.2.1,
    untouched.2.2.2.2.2.1, untouched.2.2.2.2.2.2]

@[simp] theorem returned_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (returned s) = r (.SFP reg) s := by
  simp [returned, state_simp_rules]

/-- Local observations of words saved by the wrapper's entry prologue. -/
structure SavedFrom (original s : ArmState) : Prop where
  stack : sp s + 144#64 = sp original
  words : ∀ reg displacement, (reg, displacement) ∈ saved →
    read_mem_bytes 8 (sp s + BitVec.ofNat 64 displacement) s = r (.GPR reg) original
  registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
    reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5] →
    r (.GPR reg) s = r (.GPR reg) original
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) s).setWidth 64 = (r (.SFP reg) original).setWidth 64

theorem returned_original (original s : ArmState) (savedFrom : SavedFrom original s)
    (code : s.program = original.program) (error : read_err s = .None) :
    Emit.Returned original (returned s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (returned_pc s).trans (savedFrom.words 30#5 96 (by simp [saved]))
  · exact (returned_error s).trans error
  · exact (returned_program s).trans code
  · exact (returned_sp s).trans savedFrom.stack
  · intro reg low high
    by_cases member : reg ∈ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (returned_saved s 19#5 136 (by simp [saved])).trans
          (savedFrom.words 19#5 136 (by simp [saved]))
      · exact (returned_saved s 20#5 128 (by simp [saved])).trans
          (savedFrom.words 20#5 128 (by simp [saved]))
      · exact (returned_saved s 21#5 120 (by simp [saved])).trans
          (savedFrom.words 21#5 120 (by simp [saved]))
      · exact (returned_saved s 22#5 112 (by simp [saved])).trans
          (savedFrom.words 22#5 112 (by simp [saved]))
      · exact (returned_saved s 23#5 104 (by simp [saved])).trans
          (savedFrom.words 23#5 104 (by simp [saved]))
      · exact (returned_saved s 30#5 96 (by simp [saved])).trans
          (savedFrom.words 30#5 96 (by simp [saved]))
    · have notSP : reg ≠ 31#5 := by bv_omega
      have untouched : reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5, 31#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at member ⊢
        rcases member with ⟨h19, h20, h21, h22, h23, h30⟩
        exact ⟨h19, h20, h21, h22, h23, h30, notSP⟩
      exact (returned_other s reg untouched).trans (savedFrom.registers reg low high member)
  · intro reg low high
    rw [returned_vector]
    exact savedFrom.vectors reg low high

end SszArm.Serialize.Finish
