import SszArm.HashFinalizeScalarRows3

namespace SszArm.Hash.Finalize

theorem entry_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 31#5] s (entryState s) := by
  have steps : ∀ op ∈ entryOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 31#5] t (op.effect t) := by
    intro op member t alignment
    simp only [entryOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact (scalar_p0 t alignment).weaken (by decide)
    · exact (scalar_p4 t alignment).weaken (by decide)
    · exact (scalar_p8 t alignment).weaken (by decide)
    · exact (scalar_p12 t alignment).weaken (by decide)
  simpa only [entryState] using (scalar_effect entryOps [8#5, 31#5] s aligned steps).frame

theorem guard_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [] s (guardState s) := by
  have steps : ∀ op ∈ guardOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [] t (op.effect t) := by
    intro op member t alignment
    simp only [guardOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (scalar_p16 t alignment).weaken (by decide)
    · exact (scalar_p20 t alignment).weaken (by decide)
  simpa only [guardState] using (scalar_effect guardOps [] s aligned steps).frame

theorem delimiter_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [9#5, 10#5, 31#5] s (delimiterState s) := by
  have steps : ∀ op ∈ delimiterOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [9#5, 10#5, 31#5] t (op.effect t) := by
    intro op member t alignment
    simp only [delimiterOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p24 t alignment).weaken (by decide)
    · exact (scalar_p28 t alignment).weaken (by decide)
    · exact (scalar_p32 t alignment).weaken (by decide)
    · exact (scalar_p36 t alignment).weaken (by decide)
    · exact (scalar_p40 t alignment).weaken (by decide)
    · exact (scalar_p44 t alignment).weaken (by decide)
    · exact (scalar_p48 t alignment).weaken (by decide)
    · exact (scalar_p52 t alignment).weaken (by decide)
  simpa only [delimiterState] using (scalar_effect delimiterOps [9#5, 10#5, 31#5] s aligned steps).frame

theorem prepare_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [0#5, 8#5, 19#5, 20#5] s (prepareState s) := by
  have steps : ∀ op ∈ prepareOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [0#5, 8#5, 19#5, 20#5] t (op.effect t) := by
    intro op member t alignment
    simp only [prepareOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p56 t alignment).weaken (by decide)
    · exact (scalar_p60 t alignment).weaken (by decide)
    · exact (scalar_p64 t alignment).weaken (by decide)
    · exact (scalar_p68 t alignment).weaken (by decide)
    · exact (scalar_p72 t alignment).weaken (by decide)
    · exact (scalar_p76 t alignment).weaken (by decide)
    · exact (scalar_p80 t alignment).weaken (by decide)
  simpa only [prepareState] using (scalar_effect prepareOps [0#5, 8#5, 19#5, 20#5] s aligned steps).frame

theorem overflowGuard_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [] s (overflowGuardState s) := by
  have steps : ∀ op ∈ overflowGuardOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [] t (op.effect t) := by
    intro op member t alignment
    simp only [overflowGuardOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (scalar_p84 t alignment).weaken (by decide)
    · exact (scalar_p88 t alignment).weaken (by decide)
  simpa only [overflowGuardState] using (scalar_effect overflowGuardOps [] s aligned steps).frame

theorem overflowZeroCall_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [0#5, 1#5, 2#5, 9#5, 30#5] s (overflowZeroCallState s) := by
  have steps : ∀ op ∈ overflowZeroCallOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [0#5, 1#5, 2#5, 9#5, 30#5] t (op.effect t) := by
    intro op member t alignment
    simp only [overflowZeroCallOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p92 t alignment).weaken (by decide)
    · exact (scalar_p96 t alignment).weaken (by decide)
    · exact (scalar_p100 t alignment).weaken (by decide)
    · exact (scalar_p104 t alignment).weaken (by decide)
    · exact (scalar_p108 t alignment).weaken (by decide)
  simpa only [overflowZeroCallState] using (scalar_effect overflowZeroCallOps [0#5, 1#5, 2#5, 9#5, 30#5] s aligned steps).frame

theorem overflowCompressCall_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [0#5, 1#5, 30#5] s (overflowCompressCallState s) := by
  have steps : ∀ op ∈ overflowCompressCallOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [0#5, 1#5, 30#5] t (op.effect t) := by
    intro op member t alignment
    simp only [overflowCompressCallOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact (scalar_p112 t alignment).weaken (by decide)
    · exact (scalar_p116 t alignment).weaken (by decide)
    · exact (scalar_p120 t alignment).weaken (by decide)
  simpa only [overflowCompressCallState] using (scalar_effect overflowCompressCallOps [0#5, 1#5, 30#5] s aligned steps).frame

theorem reset_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [0#5, 9#5, 10#5, 31#5] s (resetState s) := by
  have steps : ∀ op ∈ resetOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [0#5, 9#5, 10#5, 31#5] t (op.effect t) := by
    intro op member t alignment
    simp only [resetOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p124 t alignment).weaken (by decide)
    · exact (scalar_p128 t alignment).weaken (by decide)
    · exact (scalar_p132 t alignment).weaken (by decide)
    · exact (scalar_p136 t alignment).weaken (by decide)
    · exact (scalar_p140 t alignment).weaken (by decide)
    · exact (scalar_p144 t alignment).weaken (by decide)
    · exact (scalar_p148 t alignment).weaken (by decide)
    · exact (scalar_p152 t alignment).weaken (by decide)
    · exact (scalar_p156 t alignment).weaken (by decide)
    · exact (scalar_p160 t alignment).weaken (by decide)
    · exact (scalar_p164 t alignment).weaken (by decide)
  simpa only [resetState] using (scalar_effect resetOps [0#5, 9#5, 10#5, 31#5] s aligned steps).frame

theorem lastZeroCall_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [0#5, 1#5, 2#5, 8#5, 30#5] s (lastZeroCallState s) := by
  have steps : ∀ op ∈ lastZeroCallOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [0#5, 1#5, 2#5, 8#5, 30#5] t (op.effect t) := by
    intro op member t alignment
    simp only [lastZeroCallOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p168 t alignment).weaken (by decide)
    · exact (scalar_p172 t alignment).weaken (by decide)
    · exact (scalar_p176 t alignment).weaken (by decide)
    · exact (scalar_p180 t alignment).weaken (by decide)
    · exact (scalar_p184 t alignment).weaken (by decide)
  simpa only [lastZeroCallState] using (scalar_effect lastZeroCallOps [0#5, 1#5, 2#5, 8#5, 30#5] s aligned steps).frame

theorem lengthCall_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [0#5, 1#5, 8#5, 30#5] s (lengthCallState s) := by
  have steps : ∀ op ∈ lengthCallOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [0#5, 1#5, 8#5, 30#5] t (op.effect t) := by
    intro op member t alignment
    simp only [lengthCallOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p188 t alignment).weaken (by decide)
    · exact (scalar_p192 t alignment).weaken (by decide)
    · exact (scalar_p196 t alignment).weaken (by decide)
    · exact (scalar_p200 t alignment).weaken (by decide)
    · exact (scalar_p204 t alignment).weaken (by decide)
    · exact (scalar_p208 t alignment).weaken (by decide)
    · exact (scalar_p212 t alignment).weaken (by decide)
  simpa only [lengthCallState] using (scalar_effect lengthCallOps [0#5, 1#5, 8#5, 30#5] s aligned steps).frame

theorem emit0_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 11#5, 12#5] s (emit0State s) := by
  have steps : ∀ op ∈ emit0Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 11#5, 12#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit0Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p216 t alignment).weaken (by decide)
    · exact (scalar_p220 t alignment).weaken (by decide)
    · exact (scalar_p224 t alignment).weaken (by decide)
    · exact (scalar_p228 t alignment).weaken (by decide)
    · exact (scalar_p232 t alignment).weaken (by decide)
    · exact (scalar_p236 t alignment).weaken (by decide)
    · exact (scalar_p240 t alignment).weaken (by decide)
    · exact (scalar_p244 t alignment).weaken (by decide)
  simpa only [emit0State] using (scalar_effect emit0Ops [8#5, 9#5, 10#5, 11#5, 12#5] s aligned steps).frame

theorem emit1_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 10#5, 11#5, 13#5] s (emit1State s) := by
  have steps : ∀ op ∈ emit1Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 10#5, 11#5, 13#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit1Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p248 t alignment).weaken (by decide)
    · exact (scalar_p252 t alignment).weaken (by decide)
    · exact (scalar_p256 t alignment).weaken (by decide)
    · exact (scalar_p260 t alignment).weaken (by decide)
    · exact (scalar_p264 t alignment).weaken (by decide)
    · exact (scalar_p268 t alignment).weaken (by decide)
    · exact (scalar_p272 t alignment).weaken (by decide)
    · exact (scalar_p276 t alignment).weaken (by decide)
  simpa only [emit1State] using (scalar_effect emit1Ops [8#5, 10#5, 11#5, 13#5] s aligned steps).frame

theorem emit2_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 11#5, 12#5] s (emit2State s) := by
  have steps : ∀ op ∈ emit2Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 11#5, 12#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit2Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p280 t alignment).weaken (by decide)
    · exact (scalar_p284 t alignment).weaken (by decide)
    · exact (scalar_p288 t alignment).weaken (by decide)
    · exact (scalar_p292 t alignment).weaken (by decide)
    · exact (scalar_p296 t alignment).weaken (by decide)
    · exact (scalar_p300 t alignment).weaken (by decide)
    · exact (scalar_p304 t alignment).weaken (by decide)
    · exact (scalar_p308 t alignment).weaken (by decide)
  simpa only [emit2State] using (scalar_effect emit2Ops [8#5, 9#5, 10#5, 11#5, 12#5] s aligned steps).frame

theorem emit3_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 12#5] s (emit3State s) := by
  have steps : ∀ op ∈ emit3Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 12#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit3Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p312 t alignment).weaken (by decide)
    · exact (scalar_p316 t alignment).weaken (by decide)
    · exact (scalar_p320 t alignment).weaken (by decide)
    · exact (scalar_p324 t alignment).weaken (by decide)
    · exact (scalar_p328 t alignment).weaken (by decide)
    · exact (scalar_p332 t alignment).weaken (by decide)
    · exact (scalar_p336 t alignment).weaken (by decide)
    · exact (scalar_p340 t alignment).weaken (by decide)
  simpa only [emit3State] using (scalar_effect emit3Ops [8#5, 9#5, 10#5, 12#5] s aligned steps).frame

theorem emit4_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 11#5] s (emit4State s) := by
  have steps : ∀ op ∈ emit4Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 11#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit4Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p344 t alignment).weaken (by decide)
    · exact (scalar_p348 t alignment).weaken (by decide)
    · exact (scalar_p352 t alignment).weaken (by decide)
    · exact (scalar_p356 t alignment).weaken (by decide)
    · exact (scalar_p360 t alignment).weaken (by decide)
    · exact (scalar_p364 t alignment).weaken (by decide)
    · exact (scalar_p368 t alignment).weaken (by decide)
    · exact (scalar_p372 t alignment).weaken (by decide)
  simpa only [emit4State] using (scalar_effect emit4Ops [8#5, 9#5, 10#5, 11#5] s aligned steps).frame

theorem emit5_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 11#5, 12#5] s (emit5State s) := by
  have steps : ∀ op ∈ emit5Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 11#5, 12#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit5Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p376 t alignment).weaken (by decide)
    · exact (scalar_p380 t alignment).weaken (by decide)
    · exact (scalar_p384 t alignment).weaken (by decide)
    · exact (scalar_p388 t alignment).weaken (by decide)
    · exact (scalar_p392 t alignment).weaken (by decide)
    · exact (scalar_p396 t alignment).weaken (by decide)
    · exact (scalar_p400 t alignment).weaken (by decide)
    · exact (scalar_p404 t alignment).weaken (by decide)
  simpa only [emit5State] using (scalar_effect emit5Ops [8#5, 9#5, 10#5, 11#5, 12#5] s aligned steps).frame

theorem emit6_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 12#5] s (emit6State s) := by
  have steps : ∀ op ∈ emit6Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 12#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit6Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p408 t alignment).weaken (by decide)
    · exact (scalar_p412 t alignment).weaken (by decide)
    · exact (scalar_p416 t alignment).weaken (by decide)
    · exact (scalar_p420 t alignment).weaken (by decide)
    · exact (scalar_p424 t alignment).weaken (by decide)
    · exact (scalar_p428 t alignment).weaken (by decide)
    · exact (scalar_p432 t alignment).weaken (by decide)
    · exact (scalar_p436 t alignment).weaken (by decide)
  simpa only [emit6State] using (scalar_effect emit6Ops [8#5, 9#5, 12#5] s aligned steps).frame

theorem emit7_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 11#5] s (emit7State s) := by
  have steps : ∀ op ∈ emit7Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 11#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit7Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p440 t alignment).weaken (by decide)
    · exact (scalar_p444 t alignment).weaken (by decide)
    · exact (scalar_p448 t alignment).weaken (by decide)
    · exact (scalar_p452 t alignment).weaken (by decide)
    · exact (scalar_p456 t alignment).weaken (by decide)
    · exact (scalar_p460 t alignment).weaken (by decide)
    · exact (scalar_p464 t alignment).weaken (by decide)
    · exact (scalar_p468 t alignment).weaken (by decide)
  simpa only [emit7State] using (scalar_effect emit7Ops [8#5, 9#5, 10#5, 11#5] s aligned steps).frame

theorem emit8_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5, 10#5, 11#5, 12#5] s (emit8State s) := by
  have steps : ∀ op ∈ emit8Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5, 10#5, 11#5, 12#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit8Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p472 t alignment).weaken (by decide)
    · exact (scalar_p476 t alignment).weaken (by decide)
    · exact (scalar_p480 t alignment).weaken (by decide)
    · exact (scalar_p484 t alignment).weaken (by decide)
    · exact (scalar_p488 t alignment).weaken (by decide)
    · exact (scalar_p492 t alignment).weaken (by decide)
    · exact (scalar_p496 t alignment).weaken (by decide)
    · exact (scalar_p500 t alignment).weaken (by decide)
  simpa only [emit8State] using (scalar_effect emit8Ops [8#5, 9#5, 10#5, 11#5, 12#5] s aligned steps).frame

theorem emit9_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [8#5, 9#5] s (emit9State s) := by
  have steps : ∀ op ∈ emit9Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [8#5, 9#5] t (op.effect t) := by
    intro op member t alignment
    simp only [emit9Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scalar_p504 t alignment).weaken (by decide)
    · exact (scalar_p508 t alignment).weaken (by decide)
    · exact (scalar_p512 t alignment).weaken (by decide)
    · exact (scalar_p516 t alignment).weaken (by decide)
    · exact (scalar_p520 t alignment).weaken (by decide)
    · exact (scalar_p524 t alignment).weaken (by decide)
    · exact (scalar_p528 t alignment).weaken (by decide)
    · exact (scalar_p532 t alignment).weaken (by decide)
  simpa only [emit9State] using (scalar_effect emit9Ops [8#5, 9#5] s aligned steps).frame

theorem emit10_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [] s (emit10State s) := by
  have steps : ∀ op ∈ emit10Ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [] t (op.effect t) := by
    intro op member t alignment
    simp only [emit10Ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (scalar_p536 t alignment).weaken (by decide)
    · exact (scalar_p540 t alignment).weaken (by decide)
  simpa only [emit10State] using (scalar_effect emit10Ops [] s aligned steps).frame

theorem return_scalar (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarFrame [19#5, 20#5, 30#5, 31#5] s (returnState s) := by
  have steps : ∀ op ∈ returnOps, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep [19#5, 20#5, 30#5, 31#5] t (op.effect t) := by
    intro op member t alignment
    simp only [returnOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact (scalar_p544 t alignment).weaken (by decide)
    · exact (scalar_p548 t alignment).weaken (by decide)
    · exact (scalar_p552 t alignment).weaken (by decide)
  simpa only [returnState] using (scalar_effect returnOps [19#5, 20#5, 30#5, 31#5] s aligned steps).frame

end SszArm.Hash.Finalize
