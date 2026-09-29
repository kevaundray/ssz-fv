import SszArm.HashFinalizeDigestMemory

namespace SszArm.Hash.Finalize

def emit0Written : List (Fin 32) := [⟨0, by decide⟩]

structure Emit0Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = ((reverse32 words[0].toBitVec) >>> (8 : Nat)).setWidth 64
  x9 : r (.GPR 9#5) t = (reverse32 words[1].toBitVec).setWidth 64
  x10 : r (.GPR 10#5) t = outputPtr s
  x11 : r (.GPR 11#5) t = ((reverse32 words[0].toBitVec) >>> (24 : Nat)).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[0].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit0_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words) :
    Emit0Registers s (emit0State t) words ∧
    (emit0State t).mem = (emitMemory s t words emit0Written).mem := by
  have physical := g.stateBound
  have outputBound := g.outputBound
  have apart := g.outputState
  have pair0 := chaining_pair t (statePtr s + 64#64) words chaining ⟨0, by decide⟩
  have pair1 := chaining_pair t (statePtr s + 64#64) words chaining ⟨1, by decide⟩
  have pair2 := chaining_pair t (statePtr s + 64#64) words chaining ⟨2, by decide⟩
  have pair3 := chaining_pair t (statePtr s + 64#64) words chaining ⟨3, by decide⟩
  simp only [BitVec.add_zero, BitVec.add_assoc] at pair0 pair1 pair2 pair3
  constructor
  · constructor <;>
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | bv_omega)
        [emit0State, effect, emit0Ops, p216, p220, p224, p228, p232, p236, p240, p244, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit0State, effect, emit0Ops, p216, p220, p224, p228, p232, p236, p240, p244, Op.effect, exec_inst,
       emitMemory, emit0Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit1Written : List (Fin 32) := [⟨4, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩]

structure Emit1Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = ((reverse32 words[1].toBitVec) >>> (8 : Nat)).setWidth 64
  x9 : r (.GPR 9#5) t = (reverse32 words[1].toBitVec).setWidth 64
  x10 : r (.GPR 10#5) t = outputPtr s + 4#64
  x11 : r (.GPR 11#5) t = ((reverse32 words[1].toBitVec) >>> (24 : Nat)).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[0].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit1_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit0Registers s t words) :
    Emit1Registers s (emit1State t) words ∧
    (emit1State t).mem = (emitMemory s t words emit1Written).mem := by
  have physical := g.stateBound
  have outputBound := g.outputBound
  have apart := g.outputState
  rcases registers with ⟨x8, x9, x10, x11, x12⟩
  have pair0 := chaining_pair t (statePtr s + 64#64) words chaining ⟨0, by decide⟩
  have pair1 := chaining_pair t (statePtr s + 64#64) words chaining ⟨1, by decide⟩
  have pair2 := chaining_pair t (statePtr s + 64#64) words chaining ⟨2, by decide⟩
  have pair3 := chaining_pair t (statePtr s + 64#64) words chaining ⟨3, by decide⟩
  simp only [BitVec.add_zero, BitVec.add_assoc] at pair0 pair1 pair2 pair3
  constructor
  · constructor <;>
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | bv_omega)
        [emit1State, effect, emit1Ops, p248, p252, p256, p260, p264, p268, p272, p276, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit1State, effect, emit1Ops, p248, p252, p256, p260, p264, p268, p272, p276, Op.effect, exec_inst,
       emitMemory, emit1Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit2Written : List (Fin 32) := [⟨7, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩]

structure Emit2Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 8#64
  x9 : r (.GPR 9#5) t = (words[3].toBitVec).setWidth 64
  x10 : r (.GPR 10#5) t = ((reverse32 words[2].toBitVec) >>> (24 : Nat)).setWidth 64
  x11 : r (.GPR 11#5) t = (reverse32 words[2].toBitVec).setWidth 64
  x12 : r (.GPR 12#5) t = (words[2].toBitVec).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit2_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit1Registers s t words) :
    Emit2Registers s (emit2State t) words ∧
    (emit2State t).mem = (emitMemory s t words emit2Written).mem := by
  have physical := g.stateBound
  have outputBound := g.outputBound
  have apart := g.outputState
  rcases registers with ⟨x8, x9, x10, x11, x12, x13⟩
  have pair0 := chaining_pair t (statePtr s + 64#64) words chaining ⟨0, by decide⟩
  have pair1 := chaining_pair t (statePtr s + 64#64) words chaining ⟨1, by decide⟩
  have pair2 := chaining_pair t (statePtr s + 64#64) words chaining ⟨2, by decide⟩
  have pair3 := chaining_pair t (statePtr s + 64#64) words chaining ⟨3, by decide⟩
  simp only [BitVec.add_zero, BitVec.add_assoc] at pair0 pair1 pair2 pair3
  constructor
  · constructor <;>
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | bv_omega)
        [emit2State, effect, emit2Ops, p280, p284, p288, p292, p296, p300, p304, p308, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit2State, effect, emit2Ops, p280, p284, p288, p292, p296, p300, p304, p308, Op.effect, exec_inst,
       emitMemory, emit2Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit3Written : List (Fin 32) := [⟨8, by decide⟩, ⟨11, by decide⟩, ⟨10, by decide⟩]

structure Emit3Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s
  x9 : r (.GPR 9#5) t = (reverse32 words[3].toBitVec).setWidth 64
  x10 : r (.GPR 10#5) t = ((reverse32 words[2].toBitVec) >>> (8 : Nat)).setWidth 64
  x11 : r (.GPR 11#5) t = (reverse32 words[2].toBitVec).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[3].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit3_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit2Registers s t words) :
    Emit3Registers s (emit3State t) words ∧
    (emit3State t).mem = (emitMemory s t words emit3Written).mem := by
  have physical := g.stateBound
  have outputBound := g.outputBound
  have apart := g.outputState
  rcases registers with ⟨x8, x9, x10, x11, x12, x13⟩
  have pair0 := chaining_pair t (statePtr s + 64#64) words chaining ⟨0, by decide⟩
  have pair1 := chaining_pair t (statePtr s + 64#64) words chaining ⟨1, by decide⟩
  have pair2 := chaining_pair t (statePtr s + 64#64) words chaining ⟨2, by decide⟩
  have pair3 := chaining_pair t (statePtr s + 64#64) words chaining ⟨3, by decide⟩
  simp only [BitVec.add_zero, BitVec.add_assoc] at pair0 pair1 pair2 pair3
  constructor
  · constructor <;>
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | bv_omega)
        [emit3State, effect, emit3Ops, p312, p316, p320, p324, p328, p332, p336, p340, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit3State, effect, emit3Ops, p312, p316, p320, p324, p328, p332, p336, p340, Op.effect, exec_inst,
       emitMemory, emit3Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

end SszArm.Hash.Finalize
