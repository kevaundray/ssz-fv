import SszArm.CodecFixedMeasurePrologue

namespace SszArm.Codec.Fixed.MeasureFixed

open Dispatch.Block (next put)
open IsFixed (loadPair)
open Delimited (MemoryFrame Returned)

def epilogueOps : List Op := [.finish .p716, .finish .p720, .finish .p724,
  .finish .p728, .finish .p732, .finish .p736, .finish .p740]

@[irreducible] def epilogue (s : ArmState) : ArmState := block epilogueOps s

@[simp] theorem epilogue_memory (s : ArmState) : (epilogue s).mem = s.mem := by
  simp [epilogue, epilogueOps, block, Op.effect, Return.Op.effect, next, put,
    loadPair, state_simp_rules]

@[simp] theorem epilogue_program (s : ArmState) : (epilogue s).program = s.program :=
  block_program epilogueOps s

@[simp] theorem epilogue_error (s : ArmState) : read_err (epilogue s) = read_err s :=
  block_error epilogueOps s

@[simp] theorem epilogue_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (epilogue s) = r (.SFP reg) s := by
  simp [epilogue, epilogueOps, block, Op.effect, Return.Op.effect, next, put,
    loadPair, state_simp_rules]

theorem epilogue_register (s : ArmState) (reg : BitVec 5)
    (different : reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5, 30#5, 31#5]) :
    r (.GPR reg) (epilogue s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
  rcases different with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h30, h31⟩
  simp [epilogue, epilogueOps, block, Op.effect, Return.Op.effect, next, put,
    loadPair, state_simp_rules, h19, h20, h21, h22, h23, h24, h25, h26, h30, h31]

theorem epilogue_run (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 716#64) :
    run 7 s = epilogue s := by
  have pcs : PCs base epilogueOps s := by
    change r .PC s = base + 716#64 at pc
    simp [PCs, epilogueOps, Op.row, Return.Op.row, Op.effect, Return.Op.effect,
      put, next, loadPair, state_simp_rules, pc, BitVec.add_assoc]
  exact run_block epilogueOps s base code error aligned pcs

structure Context (source current : ArmState) : Prop where
  saved : Saved source current
  registers : ∀ reg : BitVec 5, 27 ≤ reg.toNat → reg.toNat ≤ 29 →
    r (.GPR reg) current = r (.GPR reg) source
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) source).setWidth 64

theorem prologue_context (s : ArmState) (low : 160 ≤ (r (.GPR 31#5) s).toNat) :
    Context s (prologue s) := by
  refine ⟨prologue_saved_state s low, ?_, ?_⟩
  · intro reg lower upper
    exact prologue_register s reg (by bv_omega)
  · intro reg lower upper
    rw [prologue_vector]

theorem epilogue_returned (source current : ArmState) (context : Context source current)
    (error : read_err current = .None) : Returned source (epilogue current) := by
  have h19 := context.saved.slots 19#5 152 (by decide)
  have h20 := context.saved.slots 20#5 144 (by decide)
  have h21 := context.saved.slots 21#5 136 (by decide)
  have h22 := context.saved.slots 22#5 128 (by decide)
  have h23 := context.saved.slots 23#5 120 (by decide)
  have h24 := context.saved.slots 24#5 112 (by decide)
  have h25 := context.saved.slots 25#5 104 (by decide)
  have h26 := context.saved.slots 26#5 96 (by decide)
  have h30 := context.saved.slots 30#5 80 (by decide)
  refine ⟨?_, (epilogue_error current).trans error, ?_, ?_, ?_⟩
  · simp [epilogue, epilogueOps, block, Op.effect, Return.Op.effect, next, put,
      loadPair, state_simp_rules, context.saved.sp, h30]
  · simp [epilogue, epilogueOps, block, Op.effect, Return.Op.effect, next, put,
      loadPair, state_simp_rules, context.saved.sp, Args.bodySP, Args.ofEntry]
  · intro reg lower upper
    have cases : reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨
        (27 ≤ reg.toNat ∧ reg.toNat ≤ 29) ∨ reg = 30#5 := by bv_omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | middle | rfl
    any_goals
      exact (epilogue_register current reg (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        bv_omega)).trans (context.registers reg middle.1 middle.2)
    all_goals
      simp [epilogue, epilogueOps, block, Op.effect, Return.Op.effect, next, put,
        loadPair, state_simp_rules, context.saved.sp, BitVec.add_assoc,
        h19, h20, h21, h22, h23, h24, h25, h26, h30]
  · intro reg lower upper
    rw [epilogue_vector]
    exact context.vectors reg lower upper

theorem epilogue_frame (s : ArmState) (writes : List Delimited.Span) :
    MemoryFrame writes s (epilogue s) := by
  intro address outside
  exact congrArg (fun memory => memory address) (epilogue_memory s)

end SszArm.Codec.Fixed.MeasureFixed
