import SszArm.NatMulWordReturnLower
import SszArm.NatAddReturnError

namespace SszArm.NatMulWord

inductive ErrorStage where
  | one | zero48 | zero32 | zero16 | pair | status | store | ret

def ErrorStage.functions (base : BitVec 64) : ErrorStage → List (ArmState → ArmState)
  | .one => [NatAdd.Op.effect base .p1248]
  | .zero48 => NatFromU128.LowerKind.zero48.ops.map (NatFromU128.Op.effect base)
  | .zero32 => NatFromU128.LowerKind.zero32.ops.map (NatFromU128.Op.effect base)
  | .zero16 => NatFromU128.LowerKind.zero16.ops.map (NatFromU128.Op.effect base)
  | .pair => PairKind.error.ops.map (Op.effect base)
  | .status => [NatAdd.Op.effect base .p1436]
  | .store => [NatAdd.Op.effect base .p1440]
  | .ret => [NatAdd.Op.effect base .p1444]

def ErrorStage.effect (base : BitVec 64) : ErrorStage → ArmState → ArmState
  | .one => NatAdd.Op.effect base .p1248
  | .zero48 => NatFromU128.block base NatFromU128.LowerKind.zero48.ops
  | .zero32 => NatFromU128.block base NatFromU128.LowerKind.zero32.ops
  | .zero16 => NatFromU128.block base NatFromU128.LowerKind.zero16.ops
  | .pair => block base PairKind.error.ops
  | .status => NatAdd.Op.effect base .p1436
  | .store => NatAdd.Op.effect base .p1440
  | .ret => NatAdd.Op.effect base .p1444

theorem ErrorStage.effect_functions (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    stage.effect base s = (stage.functions base).foldl (fun t f => f t) s := by
  cases stage <;>
    simp only [ErrorStage.effect, ErrorStage.functions, NatFromU128.block, block,
      List.foldl_map, List.foldl_cons, List.foldl_nil]

theorem ErrorStage.registers (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) (h8 : reg ≠ 8#5) :
    r (.GPR reg) (stage.effect base s) = r (.GPR reg) s := by
  cases stage
  case zero48 => exact NatFromU128.lower_registers .zero48 s base owned.space reg
  case zero32 => exact NatFromU128.lower_registers .zero32 s base owned.space reg
  case zero16 => exact NatFromU128.lower_registers .zero16 s base owned.space reg
  case pair =>
    change r (.GPR reg) (block base PairKind.error.ops s) = r (.GPR reg) s
    rw [pair_effect .error s base owned,
      r_of_w_different (show StateField.GPR reg ≠ .PC by intro h; cases h)]
    simp only [NatFromU128.scratchPair, r_of_write_mem_bytes]
  all_goals
    simp [ErrorStage.effect, NatAdd.Op.effect, NatAdd.put, NatAdd.next, state_simp_rules, h8]

theorem ErrorStage.owned (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : ReturnOwned (stage.effect base s) := by
  have out := stage.registers s base owned 0#5 (by decide)
  have sp := stage.registers s base owned 31#5 (by decide)
  exact ⟨by simpa only [sp] using owned.stack,
    by simpa only [out] using owned.output,
    by simpa only [out, sp] using owned.separate⟩

def errorStages : NatAdd.ErrorPath → List ErrorStage
  | .scratch => [.one, .zero48, .zero32, .zero16, .pair, .status, .store, .ret]
  | .sizeOverflow => [.one, .zero16, .pair, .zero32, .zero48, .status, .store, .ret]

theorem error_stages_functions (stages : List ErrorStage) (s : ArmState) (base : BitVec 64) :
    (stages.flatMap (ErrorStage.functions base)).foldl (fun t f => f t) s =
      stages.foldl (fun t stage => stage.effect base t) s := by
  induction stages generalizing s with
  | nil => rfl
  | cons stage stages ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
    rw [← ErrorStage.effect_functions, ih]

theorem add_error_eq_stages (path : NatAdd.ErrorPath) (s : ArmState) (base : BitVec 64) :
    NatAdd.errorResult path base s =
      (errorStages path).foldl (fun t stage => stage.effect base t) s := by
  have effects : path.ops.map (NatAdd.Op.effect base) =
      (errorStages path).flatMap (ErrorStage.functions base) := by
    cases path <;>
      simp only [NatAdd.ErrorPath.ops, errorStages, List.flatMap_cons, List.flatMap_nil,
        ErrorStage.functions, NatFromU128.LowerKind.ops,
        PairKind.ops, PairKind.enterOps, PairKind.storeOps, PairKind.restoreOps,
        List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.cons.injEq, and_true, true_and]
    all_goals repeat' apply And.intro
    all_goals
      funext t
      simp only [NatAdd.Op.effect, NatFromU128.Op.effect, Op.effect,
        NatAdd.put, NatAdd.next, NatFromU128.put, NatFromU128.next, put, next,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have folded := congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects
  simpa only [NatAdd.errorResult, NatAdd.block, List.foldl_map, error_stages_functions] using folded

theorem error_stages_registers (stages : List ErrorStage) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) (h8 : reg ≠ 8#5) :
    r (.GPR reg) (stages.foldl (fun t stage => stage.effect base t) s) = r (.GPR reg) s := by
  induction stages generalizing s with
  | nil => rfl
  | cons stage stages ih =>
    exact (ih (stage.effect base s) (stage.owned s base owned)).trans
      (stage.registers s base owned reg h8)

theorem add_error_registers (path : NatAdd.ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) (h8 : reg ≠ 8#5) :
    r (.GPR reg) (NatAdd.errorResult path base s) = r (.GPR reg) s := by
  rw [add_error_eq_stages]
  exact error_stages_registers (errorStages path) s base owned reg h8

end SszArm.NatMulWord
