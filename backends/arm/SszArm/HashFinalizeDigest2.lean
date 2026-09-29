import SszArm.HashFinalizeDigest1

namespace SszArm.Hash.Finalize

def emit8Written : List (Fin 32) := [⟨24, by decide⟩, ⟨27, by decide⟩]

structure Emit8Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 24#64
  x9 : r (.GPR 9#5) t = ((reverse32 words[6].toBitVec) >>> (8 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (reverse32 words[7].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = ((reverse32 words[7].toBitVec) >>> (16 : Nat)).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[6].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit8_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit7Registers s t words) :
    Emit8Registers s (emit8State t) words ∧
    (emit8State t).mem = (emitMemory s t words emit8Written).mem := by
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
        [emit8State, effect, emit8Ops, p472, p476, p480, p484, p488, p492, p496, p500, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit8State, effect, emit8Ops, p472, p476, p480, p484, p488, p492, p496, p500, Op.effect, exec_inst,
       emitMemory, emit8Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit9Written : List (Fin 32) := [⟨26, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩]

structure Emit9Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 28#64
  x9 : r (.GPR 9#5) t = ((reverse32 words[7].toBitVec) >>> (8 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (reverse32 words[7].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = ((reverse32 words[7].toBitVec) >>> (16 : Nat)).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[6].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit9_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit8Registers s t words) :
    Emit9Registers s (emit9State t) words ∧
    (emit9State t).mem = (emitMemory s t words emit9Written).mem := by
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
        [emit9State, effect, emit9Ops, p504, p508, p512, p516, p520, p524, p528, p532, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit9State, effect, emit9Ops, p504, p508, p512, p516, p520, p524, p528, p532, Op.effect, exec_inst,
       emitMemory, emit9Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit10Written : List (Fin 32) := [⟨30, by decide⟩, ⟨29, by decide⟩]

structure Emit10Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 28#64
  x9 : r (.GPR 9#5) t = ((reverse32 words[7].toBitVec) >>> (8 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (reverse32 words[7].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = ((reverse32 words[7].toBitVec) >>> (16 : Nat)).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[6].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit10_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit9Registers s t words) :
    Emit10Registers s (emit10State t) words ∧
    (emit10State t).mem = (emitMemory s t words emit10Written).mem := by
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
        [emit10State, effect, emit10Ops, p536, p540, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit10State, effect, emit10Ops, p536, p540, Op.effect, exec_inst,
       emitMemory, emit10Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

end SszArm.Hash.Finalize
