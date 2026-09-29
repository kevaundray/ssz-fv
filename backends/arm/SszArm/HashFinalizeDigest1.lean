import SszArm.HashFinalizeDigest0

namespace SszArm.Hash.Finalize

def emit4Written : List (Fin 32) := [⟨9, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨13, by decide⟩]

structure Emit4Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 12#64
  x9 : r (.GPR 9#5) t = ((reverse32 words[3].toBitVec) >>> (8 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (words[5].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = (words[4].toBitVec).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[3].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit4_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit3Registers s t words) :
    Emit4Registers s (emit4State t) words ∧
    (emit4State t).mem = (emitMemory s t words emit4Written).mem := by
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
        [emit4State, effect, emit4Ops, p344, p348, p352, p356, p360, p364, p368, p372, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit4State, effect, emit4Ops, p344, p348, p352, p356, p360, p364, p368, p372, Op.effect, exec_inst,
       emitMemory, emit4Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit5Written : List (Fin 32) := [⟨14, by decide⟩, ⟨16, by decide⟩]

structure Emit5Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 16#64
  x9 : r (.GPR 9#5) t = ((reverse32 words[4].toBitVec) >>> (24 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (reverse32 words[5].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = (reverse32 words[4].toBitVec).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[4].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit5_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit4Registers s t words) :
    Emit5Registers s (emit5State t) words ∧
    (emit5State t).mem = (emitMemory s t words emit5Written).mem := by
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
        [emit5State, effect, emit5Ops, p376, p380, p384, p388, p392, p396, p400, p404, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit5State, effect, emit5Ops, p376, p380, p384, p388, p392, p396, p400, p404, Op.effect, exec_inst,
       emitMemory, emit5Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit6Written : List (Fin 32) := [⟨19, by decide⟩, ⟨18, by decide⟩, ⟨17, by decide⟩]

structure Emit6Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s + 20#64
  x9 : r (.GPR 9#5) t = ((reverse32 words[5].toBitVec) >>> (24 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (reverse32 words[5].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = (reverse32 words[4].toBitVec).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[5].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit6_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit5Registers s t words) :
    Emit6Registers s (emit6State t) words ∧
    (emit6State t).mem = (emitMemory s t words emit6Written).mem := by
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
        [emit6State, effect, emit6Ops, p408, p412, p416, p420, p424, p428, p432, p436, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit6State, effect, emit6Ops, p408, p412, p416, p420, p424, p428, p432, p436, Op.effect, exec_inst,
       emitMemory, emit6Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]


def emit7Written : List (Fin 32) := [⟨20, by decide⟩, ⟨23, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

structure Emit7Registers (s t : ArmState) (words : Vector UInt32 8) : Prop where
  x8 : r (.GPR 8#5) t = outputPtr s
  x9 : r (.GPR 9#5) t = ((reverse32 words[5].toBitVec) >>> (8 : Nat)).setWidth 64
  x10 : r (.GPR 10#5) t = (words[7].toBitVec).setWidth 64
  x11 : r (.GPR 11#5) t = (reverse32 words[6].toBitVec).setWidth 64
  x12 : r (.GPR 12#5) t = ((reverse32 words[5].toBitVec) >>> (16 : Nat)).setWidth 64
  x13 : r (.GPR 13#5) t = ((reverse32 words[1].toBitVec) >>> (16 : Nat)).setWidth 64

theorem emit7_observe (s t : ArmState) (words : Vector UInt32 8)
    (g : Geometry s) (live : Live s t)
    (chaining : ChainingAt t (statePtr s + 64#64) words)
    (registers : Emit6Registers s t words) :
    Emit7Registers s (emit7State t) words ∧
    (emit7State t).mem = (emitMemory s t words emit7Written).mem := by
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
        [emit7State, effect, emit7Ops, p440, p444, p448, p452, p456, p460, p464, p468, Op.effect, exec_inst,
         state_simp_rules, bitvec_rules, minimal_theory, live.output, live.state,
         x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
         lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.add_assoc]
  · simp (config := {decide := true, instances := true})
      (disch := first | assumption | bv_omega)
      [emit7State, effect, emit7Ops, p440, p444, p448, p452, p456, p460, p464, p468, Op.effect, exec_inst,
       emitMemory, emit7Written, digestOctet, state_simp_rules, bitvec_rules, minimal_theory,
       live.output, live.state, x8, x9, x10, x11, x12, x13, pair0, pair1, pair2, pair3, rev_vector, ← reverse32,
       lsr8_ubfm, lsr16_ubfm, lsr24_ubfm, BitVec.extractLsByte,
       BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.add_assoc]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

end SszArm.Hash.Finalize
