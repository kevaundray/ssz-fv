import SszArm.NatFromU128Lower
import SszNatArithmeticMemory

namespace SszArm.NatFromU128

open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

/-- Memory-only normal forms keep execution-state expansion out of observations. -/
def smallMemory (s : ArmState) : ArmState :=
  lowerMemory .smallStatus (lowerMemory .smallPair s)

def failureMemory (s : ArmState) : ArmState :=
  let prepared := w (.GPR 9#5) 1#64 (w (.GPR 8#5) 32768#64 s)
  write_mem_bytes 4 (r (.GPR 0#5) s + 64#64) 32768#32
    (lowerMemory .errorPair (lowerMemory .zero16
      (lowerMemory .zero32 (lowerMemory .zero48 prepared))))

def commitMemory (s : ArmState) : ArmState :=
  let pointer := r (.GPR 9#5) s + r (.GPR 10#5) s
  write_mem_bytes 16 (r (.GPR 0#5) s) (2#64 ++ pointer)
    (write_mem_bytes 16 pointer (r (.GPR 3#5) s ++ r (.GPR 2#5) s)
      (write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (r (.GPR 11#5) s) s))

def wideMemory (s : ArmState) : ArmState :=
  let prepared := w (.GPR 2#5) 2#64
    (w (.GPR 9#5) (r (.GPR 9#5) s + r (.GPR 10#5) s) (commitMemory s))
  lowerMemory .wideStatus prepared

inductive Body where
  | small | failure | wide
  deriving DecidableEq

def Body.entry : Body → Nat
  | .small => 4 | .failure => 220 | .wide => 156

def Body.ops : Body → List Op
  | .small => LowerKind.smallPair.ops ++ LowerKind.smallStatus.ops ++ [.p84]
  | .failure => [.p220, .p224] ++ LowerKind.zero48.ops ++ LowerKind.zero32.ops ++
      LowerKind.zero16.ops ++ LowerKind.errorPair.ops ++ [.p412, .p416]
  | .wide => [.p156, .p160, .p164, .p168, .p172] ++ LowerKind.wideStatus.ops ++ [.p216]

def Body.memory : Body → ArmState → ArmState
  | .small => smallMemory | .failure => failureMemory | .wide => wideMemory

/-- A compact final state retains the exact physical write sequence, including
both full payload words and the scratch saves on every lowering sequence. -/
def Body.final (body : Body) (s : ArmState) : ArmState :=
  w .PC (r (.GPR 30#5) s) (body.memory s)

private theorem lowerMemory_gpr (kind : LowerKind) (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (lowerMemory kind s) = r (.GPR reg) s := by
  cases kind <;> simp [lowerMemory, lowerSaved, state_simp_rules]

private theorem lowerMemory_space (kind : LowerKind) (s : ArmState) (space : Space s) :
    Space (lowerMemory kind s) := by
  exact ⟨by simpa only [lowerMemory_gpr] using space.stack,
    by simpa only [lowerMemory_gpr] using space.output,
    by simpa only [lowerMemory_gpr] using space.separate⟩

private theorem lowerMemory_pc_write (kind : LowerKind) (s : ArmState) (pc : BitVec 64) :
    lowerMemory kind (w .PC pc s) = w .PC pc (lowerMemory kind s) := by
  cases kind <;> simp [lowerMemory, lowerSaved, state_simp_rules,
    store_field_write]

/-- The five success instructions commit the cursor, both limbs, and the pair. -/
theorem commit_effect (s : ArmState) (base : BitVec 64) :
    block base [.p156, .p160, .p164, .p168, .p172] s =
      w .PC (read_pc s + 20#64)
        (w (.GPR 2#5) 2#64 (w (.GPR 9#5)
          (r (.GPR 9#5) s + r (.GPR 10#5) s) (commitMemory s))) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;> simp [block, Op.effect, put, next, commitMemory,
      state_simp_rules, BitVec.add_assoc, store_field_write]
    all_goals
      rename_i reg
      by_cases h2 : reg = 2#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h9 : reg = 9#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · simp (disch := simp_all) [state_simp_rules]
  · simp [block, Op.effect, put, next, commitMemory, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [block, Op.effect, put, next, commitMemory, state_simp_rules,
      ArmState.mem_w_eq_mem, store_field_write, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

/-- Memory and register consequences are proved once on compact blocks, never
by repeatedly expanding a 50-instruction raw machine state. -/
theorem body_effect (body : Body) (s : ArmState) (base : BitVec 64)
    (space : Space s) : block base body.ops s = body.final s := by
  have splitBlock (a b : List Op) (t : ArmState) :
      block base (a ++ b) t = block base b (block base a t) := by
    simp only [block, List.foldl_append]
  have spPC (t : ArmState) (pc : BitVec 64) (h : Space t) : Space (w .PC pc t) := by
    exact ⟨by simpa [state_simp_rules] using h.stack,
      by simpa [state_simp_rules] using h.output,
      by simpa [state_simp_rules] using h.separate⟩
  cases body
  · simp only [Body.ops, splitBlock]
    rw [lower_effect .smallPair s base space]
    rw [lower_effect .smallStatus _ base
      (spPC _ _ (lowerMemory_space .smallPair s space))]
    simp [block, Op.effect, Body.final, Body.memory, smallMemory,
      lowerMemory_pc_write, lowerMemory_gpr, state_simp_rules]
  · simp only [Body.ops, splitBlock]
    have headEq : block base [.p220, .p224] s =
        w .PC (read_pc s + 8#64) (w (.GPR 9#5) 1#64 (w (.GPR 8#5) 32768#64 s)) := by
      apply state_eq_iff_components_eq.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro f
        cases f <;> simp [block, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]
        all_goals
          rename_i reg
          by_cases h8 : reg = 8#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · by_cases h9 : reg = 9#5
            · subst reg; simp (config := {decide := true}) [state_simp_rules]
            · simp (disch := simp_all) [state_simp_rules]
      · simp [block, Op.effect, put, next, state_simp_rules]
      · simp [block, Op.effect, put, next, state_simp_rules]
    rw [headEq]
    have prepared : Space (w (.GPR 9#5) 1#64 (w (.GPR 8#5) 32768#64 s)) := by
      exact ⟨by simpa [state_simp_rules] using space.stack,
        by simpa [state_simp_rules] using space.output,
        by simpa [state_simp_rules] using space.separate⟩
    rw [lower_effect .zero48 _ base (spPC _ _ prepared)]
    rw [lower_effect .zero32 _ base (spPC _ _ (lowerMemory_space _ _ (spPC _ _ prepared)))]
    rw [lower_effect .zero16 _ base
      (spPC _ _ (lowerMemory_space _ _ (spPC _ _ (lowerMemory_space _ _ (spPC _ _ prepared)))))]
    rw [lower_effect .errorPair _ base
      (spPC _ _ (lowerMemory_space _ _ (spPC _ _ (lowerMemory_space _ _
        (spPC _ _ (lowerMemory_space _ _ (spPC _ _ prepared)))))))]
    simp [block, Op.effect, next, Body.final, Body.memory, failureMemory,
      lowerMemory_pc_write, lowerMemory_gpr, state_simp_rules,
      store_field_write]
  · simp only [Body.ops, splitBlock]
    rw [commit_effect]
    have prepared : Space (w (.GPR 2#5) 2#64 (w (.GPR 9#5)
        (r (.GPR 9#5) s + r (.GPR 10#5) s) (commitMemory s))) := by
      exact ⟨by simpa [commitMemory, state_simp_rules] using space.stack,
        by simpa [commitMemory, state_simp_rules] using space.output,
        by simpa [commitMemory, state_simp_rules] using space.separate⟩
    rw [lower_effect .wideStatus _ base (spPC _ _ prepared)]
    simp [block, Op.effect, Body.final, Body.memory, wideMemory,
      lowerMemory_pc_write, lowerMemory_gpr, commitMemory, state_simp_rules]

end SszArm.NatFromU128
