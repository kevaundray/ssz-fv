import SszArm.HashFinalizeInstructions
import SszArm.BoolAlignment

namespace SszArm.Hash.Finalize

def entryOps : List Op := [p0, p4, p8, p12]

@[irreducible] def entryState (s : ArmState) : ArmState := effect entryOps s

theorem entry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 0#64) :
    run 4 s = entryState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base entryOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, entryOps, p0, p4, p8, p12, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [entryState, entryOps, List.length_cons, List.length_nil] using
    runs entryOps s base code follows

def guardOps : List Op := [p16, p20]

@[irreducible] def guardState (s : ArmState) : ArmState := effect guardOps s

theorem guard_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 16#64) :
    run 2 s = guardState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base guardOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, guardOps, p16, p20, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [guardState, guardOps, List.length_cons, List.length_nil] using
    runs guardOps s base code follows

def delimiterOps : List Op := [p24, p28, p32, p36, p40, p44, p48, p52]

@[irreducible] def delimiterState (s : ArmState) : ArmState := effect delimiterOps s

theorem delimiter_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 24#64) :
    run 8 s = delimiterState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base delimiterOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, delimiterOps, p24, p28, p32, p36, p40, p44, p48, p52, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [delimiterState, delimiterOps, List.length_cons, List.length_nil] using
    runs delimiterOps s base code follows

def prepareOps : List Op := [p56, p60, p64, p68, p72, p76, p80]

@[irreducible] def prepareState (s : ArmState) : ArmState := effect prepareOps s

theorem prepare_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 56#64) :
    run 7 s = prepareState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base prepareOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, prepareOps, p56, p60, p64, p68, p72, p76, p80, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [prepareState, prepareOps, List.length_cons, List.length_nil] using
    runs prepareOps s base code follows

def overflowGuardOps : List Op := [p84, p88]

@[irreducible] def overflowGuardState (s : ArmState) : ArmState := effect overflowGuardOps s

theorem overflowGuard_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 84#64) :
    run 2 s = overflowGuardState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base overflowGuardOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, overflowGuardOps, p84, p88, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [overflowGuardState, overflowGuardOps, List.length_cons, List.length_nil] using
    runs overflowGuardOps s base code follows

def overflowZeroCallOps : List Op := [p92, p96, p100, p104, p108]

@[irreducible] def overflowZeroCallState (s : ArmState) : ArmState := effect overflowZeroCallOps s

theorem overflowZeroCall_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 92#64) :
    run 5 s = overflowZeroCallState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base overflowZeroCallOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, overflowZeroCallOps, p92, p96, p100, p104, p108, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [overflowZeroCallState, overflowZeroCallOps, List.length_cons, List.length_nil] using
    runs overflowZeroCallOps s base code follows

def overflowCompressCallOps : List Op := [p112, p116, p120]

@[irreducible] def overflowCompressCallState (s : ArmState) : ArmState := effect overflowCompressCallOps s

theorem overflowCompressCall_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 112#64) :
    run 3 s = overflowCompressCallState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base overflowCompressCallOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, overflowCompressCallOps, p112, p116, p120, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [overflowCompressCallState, overflowCompressCallOps, List.length_cons, List.length_nil] using
    runs overflowCompressCallOps s base code follows

def resetOps : List Op := [p124, p128, p132, p136, p140, p144, p148, p152, p156, p160, p164]

@[irreducible] def resetState (s : ArmState) : ArmState := effect resetOps s

theorem reset_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 124#64) :
    run 11 s = resetState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base resetOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, resetOps, p124, p128, p132, p136, p140, p144, p148, p152, p156, p160, p164, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [resetState, resetOps, List.length_cons, List.length_nil] using
    runs resetOps s base code follows

def lastZeroCallOps : List Op := [p168, p172, p176, p180, p184]

@[irreducible] def lastZeroCallState (s : ArmState) : ArmState := effect lastZeroCallOps s

theorem lastZeroCall_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 168#64) :
    run 5 s = lastZeroCallState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base lastZeroCallOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, lastZeroCallOps, p168, p172, p176, p180, p184, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [lastZeroCallState, lastZeroCallOps, List.length_cons, List.length_nil] using
    runs lastZeroCallOps s base code follows

def lengthCallOps : List Op := [p188, p192, p196, p200, p204, p208, p212]

@[irreducible] def lengthCallState (s : ArmState) : ArmState := effect lengthCallOps s

theorem lengthCall_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 188#64) :
    run 7 s = lengthCallState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base lengthCallOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, lengthCallOps, p188, p192, p196, p200, p204, p208, p212, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [lengthCallState, lengthCallOps, List.length_cons, List.length_nil] using
    runs lengthCallOps s base code follows

def emit0Ops : List Op := [p216, p220, p224, p228, p232, p236, p240, p244]

@[irreducible] def emit0State (s : ArmState) : ArmState := effect emit0Ops s

theorem emit0_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 216#64) :
    run 8 s = emit0State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit0Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit0Ops, p216, p220, p224, p228, p232, p236, p240, p244, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit0State, emit0Ops, List.length_cons, List.length_nil] using
    runs emit0Ops s base code follows

def emit1Ops : List Op := [p248, p252, p256, p260, p264, p268, p272, p276]

@[irreducible] def emit1State (s : ArmState) : ArmState := effect emit1Ops s

theorem emit1_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 248#64) :
    run 8 s = emit1State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit1Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit1Ops, p248, p252, p256, p260, p264, p268, p272, p276, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit1State, emit1Ops, List.length_cons, List.length_nil] using
    runs emit1Ops s base code follows

def emit2Ops : List Op := [p280, p284, p288, p292, p296, p300, p304, p308]

@[irreducible] def emit2State (s : ArmState) : ArmState := effect emit2Ops s

theorem emit2_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 280#64) :
    run 8 s = emit2State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit2Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit2Ops, p280, p284, p288, p292, p296, p300, p304, p308, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit2State, emit2Ops, List.length_cons, List.length_nil] using
    runs emit2Ops s base code follows

def emit3Ops : List Op := [p312, p316, p320, p324, p328, p332, p336, p340]

@[irreducible] def emit3State (s : ArmState) : ArmState := effect emit3Ops s

theorem emit3_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 312#64) :
    run 8 s = emit3State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit3Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit3Ops, p312, p316, p320, p324, p328, p332, p336, p340, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit3State, emit3Ops, List.length_cons, List.length_nil] using
    runs emit3Ops s base code follows

def emit4Ops : List Op := [p344, p348, p352, p356, p360, p364, p368, p372]

@[irreducible] def emit4State (s : ArmState) : ArmState := effect emit4Ops s

theorem emit4_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 344#64) :
    run 8 s = emit4State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit4Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit4Ops, p344, p348, p352, p356, p360, p364, p368, p372, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit4State, emit4Ops, List.length_cons, List.length_nil] using
    runs emit4Ops s base code follows

def emit5Ops : List Op := [p376, p380, p384, p388, p392, p396, p400, p404]

@[irreducible] def emit5State (s : ArmState) : ArmState := effect emit5Ops s

theorem emit5_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 376#64) :
    run 8 s = emit5State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit5Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit5Ops, p376, p380, p384, p388, p392, p396, p400, p404, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit5State, emit5Ops, List.length_cons, List.length_nil] using
    runs emit5Ops s base code follows

def emit6Ops : List Op := [p408, p412, p416, p420, p424, p428, p432, p436]

@[irreducible] def emit6State (s : ArmState) : ArmState := effect emit6Ops s

theorem emit6_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 408#64) :
    run 8 s = emit6State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit6Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit6Ops, p408, p412, p416, p420, p424, p428, p432, p436, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit6State, emit6Ops, List.length_cons, List.length_nil] using
    runs emit6Ops s base code follows

def emit7Ops : List Op := [p440, p444, p448, p452, p456, p460, p464, p468]

@[irreducible] def emit7State (s : ArmState) : ArmState := effect emit7Ops s

theorem emit7_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 440#64) :
    run 8 s = emit7State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit7Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit7Ops, p440, p444, p448, p452, p456, p460, p464, p468, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit7State, emit7Ops, List.length_cons, List.length_nil] using
    runs emit7Ops s base code follows

def emit8Ops : List Op := [p472, p476, p480, p484, p488, p492, p496, p500]

@[irreducible] def emit8State (s : ArmState) : ArmState := effect emit8Ops s

theorem emit8_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 472#64) :
    run 8 s = emit8State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit8Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit8Ops, p472, p476, p480, p484, p488, p492, p496, p500, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit8State, emit8Ops, List.length_cons, List.length_nil] using
    runs emit8Ops s base code follows

def emit9Ops : List Op := [p504, p508, p512, p516, p520, p524, p528, p532]

@[irreducible] def emit9State (s : ArmState) : ArmState := effect emit9Ops s

theorem emit9_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 504#64) :
    run 8 s = emit9State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit9Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit9Ops, p504, p508, p512, p516, p520, p524, p528, p532, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit9State, emit9Ops, List.length_cons, List.length_nil] using
    runs emit9Ops s base code follows

def emit10Ops : List Op := [p536, p540]

@[irreducible] def emit10State (s : ArmState) : ArmState := effect emit10Ops s

theorem emit10_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 536#64) :
    run 2 s = emit10State s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base emit10Ops s := by
    simp (config := {decide := true, instances := true})
      [Follows, emit10Ops, p536, p540, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [emit10State, emit10Ops, List.length_cons, List.length_nil] using
    runs emit10Ops s base code follows

def returnOps : List Op := [p544, p548, p552]

@[irreducible] def returnState (s : ArmState) : ArmState := effect returnOps s

theorem return_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 544#64) :
    run 3 s = returnState s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower16 := BoolCodec.aligned_sub16 _ stack
  have lower32 := BoolCodec.aligned_sub32 _ stack
  have follows : Follows base returnOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, returnOps, p544, p548, p552, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower16, lower32,
       error, pc, BitVec.add_assoc]
  simpa only [returnState, returnOps, List.length_cons, List.length_nil] using
    runs returnOps s base code follows

end SszArm.Hash.Finalize
