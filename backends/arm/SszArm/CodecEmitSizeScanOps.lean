import SszArm.CodecLinkedEmitParts
import SszArm.EmitUintScan

namespace SszArm.Codec.Emit.SizeScan

open SszArm.Emit.Uint

/-- The inline emitter scan uses the established narrowing effects. Only its
zero-count branch has a different relative displacement. -/
def allowed : List WidthOp :=
  [.p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108, .p112, .p116,
    .p120, .p124, .p128]

def row (op : WidthOp) : Nat × BitVec 32 :=
  match op with
  | .p84 => (196, 0x54000200#32)
  | _ => (op.row.1 + 112, op.row.2)

def effect (base : BitVec 64) (op : WidthOp) (s : ArmState) : ArmState :=
  match op with
  | .p84 => w .PC (if r (.FLAG .Z) s = 1#1 then base + 260#64 else base + 200#64) s
  | _ => op.effect (base + 112#64) s

theorem step (s : ArmState) (base : BitVec 64) (op : WidthOp)
    (member : op ∈ allowed) (code : Linked.EmitParts.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row op).1) :
    stepi s = effect base op s := by
  have memberRow : row op ∈ Linked.EmitParts.chunk0 := by
    cases op <;> simp_all only [allowed, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_false, false_or, or_self]
    all_goals decide
  have fetched := Linked.EmitParts.chunk0_codeAt code (row op) memberRow
  cases op <;> simp_all only [allowed, List.mem_cons, List.not_mem_nil,
    reduceCtorEq, or_false, false_or, or_self]
  all_goals
    simp only [row, WidthOp.row] at fetched pc
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [effect, WidthOp.effect, put, next, SszArm.Emit.Dispatch.next,
        exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        aligned, pc, BitVec.add_assoc, UintCodec.uint_lsl3_mask, UintCodec.uint_and_ones,
        BitVec.setWidth_eq, BitVec.sub_eq_add_neg, apply_ite]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem effect_program (base : BitVec 64) (op : WidthOp) (s : ArmState) :
    (effect base op s).program = s.program := by
  cases op <;> simp [effect, state_simp_rules]

@[simp] theorem effect_error (base : BitVec 64) (op : WidthOp) (s : ArmState) :
    read_err (effect base op s) = read_err s := by
  have previous := WidthOp.error op (base + 112#64) s
  cases op <;> first
    | exact previous
    | simp [effect, state_simp_rules]

theorem effect_aligned (base : BitVec 64) (op : WidthOp) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (effect base op s) := by
  have previous := WidthOp.aligned op (base + 112#64) s aligned
  cases op <;> first
    | exact previous
    | simpa [effect, CheckSPAlignment, state_simp_rules] using aligned

def block (base : BitVec 64) (ops : List WidthOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => effect base op t) s

def Follows (base : BitVec 64) : List WidthOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 (row op).1 ∧
      Follows base ops (effect base op s)

theorem runs (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (members : ∀ op ∈ ops, op ∈ allowed) (code : Linked.EmitParts.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (effect base op s)
    rw [run, step s base op (members _ List.mem_cons_self) code error aligned follows.1]
    apply ih _ (fun child member => members child (List.mem_cons_of_mem _ member))
      (by simpa only [Linked.EmitParts.CodeAt, Linked.WordsAt, effect_program] using code)
      ((effect_error _ _ _).trans error) (effect_aligned _ _ _ aligned) follows.2

def pureOps : List WidthOp := [.p80, .p84, .p120, .p124, .p128]

theorem pure_frame (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (members : ∀ op ∈ ops, op ∈ pureOps) : NatNarrow.Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := members op List.mem_cons_self
    have frame : NatNarrow.Frame s (effect base op s) := by
      cases op <;> simp_all only [pureOps, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact effect_program _ _ _
        · exact effect_error _ _ _
        · intro reg outside
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp (disch := simp_all) [effect, WidthOp.effect, put, next,
            SszArm.Emit.Dispatch.next, state_simp_rules]
        · intro reg
          simp [effect, WidthOp.effect, put, next, SszArm.Emit.Dispatch.next, state_simp_rules]
        · intro address outside
          simp [effect, WidthOp.effect, put, next, SszArm.Emit.Dispatch.next, state_simp_rules]
    exact frame.trans (ih _ (fun child member => members child (List.mem_cons_of_mem _ member)))

theorem frame_code {s t : ArmState} (frame : NatNarrow.Frame s t) {base : BitVec 64}
    (code : Linked.EmitParts.CodeAt s base) : Linked.EmitParts.CodeAt t base := by
  simpa only [Linked.EmitParts.CodeAt, Linked.WordsAt, frame.program] using code

/-- The eight save/load/restore instructions are byte-identical to the checked
primitive narrowing provider; their pure state expression is reused verbatim. -/
theorem load_run (s : ArmState) (base limb : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 200#64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (loaded : read_mem_bytes 8 (r (.GPR 8#5) s + (r (.GPR 10#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb) :
    run 8 s = scanLoadResult s (base + 112#64) limb := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  change r .PC s = _ at pc
  have follows : Follows base scanLoadOps s := by
    simp [scanLoadOps, Follows, row, effect, WidthOp.row, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, state_simp_rules, pc, BitVec.add_assoc]
  rw [show 8 = scanLoadOps.length by rfl,
    runs base scanLoadOps s (by decide) code error aligned follows]
  simp only [NatCompare.saved] at loaded restored
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases dest : reg = 11#5 <;> by_cases temp : reg = 9#5 <;>
        by_cases sp : reg = 31#5 <;> (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect, put, next,
            SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules,
            NatCompare.read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect, put, next,
          SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules,
          NatCompare.read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg => simp [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect,
        put, next, SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | FLAG flag => simp [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect,
        put, next, SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | ERR => simp [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect,
        put, next, SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · simp [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · intro n address
    simp [scanLoadResult, scanLoadOps, block, effect, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

end SszArm.Codec.Emit.SizeScan
