import SszArm.IndicesElementTypeState

set_option autoImplicit false

namespace SszArm.Indices.ElementType

open SszNative.Codec (Desc)
open SszNative.Indices (PathStep)

def IsBitShape : Desc → Prop
  | .primitive (.bitVector _) | .primitive (.bitList _)
  | .primitive (.progressiveBitList _) => True
  | _ => False

private theorem bit_element (shape : Desc) (step : PathStep) (bits : IsBitShape shape) :
    SszNative.Indices.elementType shape step = .ok (.primitive .bool) := by
  cases shape with
  | primitive primitive =>
      cases primitive <;> simp_all [IsBitShape, SszNative.Indices.elementType]
  | vector _ _ | list _ _ | progressiveList _ _ | container _
  | progressiveContainer _ _ | compatibleUnion _ => exact False.elim bits

private theorem bit_destination (shape : Desc) (step : PathStep) (bits : IsBitShape shape) :
    (Dispatch.Kind.ofDesc shape).destination (stepPosition step) = 60 ∧
    ((Dispatch.Kind.ofDesc shape).ops (stepPosition step)).length = 6 := by
  cases shape with
  | primitive primitive =>
      cases primitive <;>
        simp_all [IsBitShape, Dispatch.Kind.ofDesc, Dispatch.Kind.destination,
          Dispatch.Kind.ops]
  | vector _ _ | list _ _ | progressiveList _ _ | container _
  | progressiveContainer _ _ | compatibleUnion _ => exact False.elim bits

private theorem frame_read {s t : ArmState} {spans : List Delimited.Span}
    (frame : Delimited.MemoryFrame spans s t) (address : BitVec 64)
    (bound : address.toNat + 8 ≤ 2^64)
    (protected : Delimited.Protected spans address.toNat 8) :
    read_mem_bytes 8 address t = read_mem_bytes 8 address s := by
  have same := frame.load address.toNat 8 bound protected
  apply BitVec.eq_of_toNat_eq
  simpa only [UintCodec.widthLoad, Option.some.injEq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using same

private theorem body_saved {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : Owned s shape step) :
    let body := dispatched s shape step
    let final := BooleanBody.block BooleanBody.ops body
    read_mem_bytes 8 (r (.GPR 31#5) body) final = r (.GPR 30#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) body + 8#64) final = r (.GPR 19#5) s := by
  dsimp only
  have low := owned.stackLow
  have bound := (r (.GPR 31#5) s).isLt
  have separate := owned.outputStack
  have out := dispatched_register s shape step 0#5 (by decide)
  have sp := dispatched_sp s shape step
  have pointer : (r (.GPR 31#5) s - 16#64).toNat =
      (r (.GPR 31#5) s).toNat - 16 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have nextPointer : (r (.GPR 31#5) s - 16#64 + 8#64).toNat =
      (r (.GPR 31#5) s).toNat - 8 := by
    simp only [BitVec.toNat_add, pointer, BitVec.toNat_ofNat]
    omega
  have protected (offset : Nat) (which : offset = 0 ∨ offset = 8) :
      Delimited.Protected (BooleanBody.writes (dispatched s shape step))
        ((r (.GPR 31#5) s).toNat - 16 + offset) 8 := by
    right
    intro span member
    simp only [BooleanBody.writes, out, sp, pointer, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp only [Prod.fst, Prod.snd] <;> omega
  have lowRead := frame_read (BooleanBody.body_frame owned.bodyGeometry)
    (r (.GPR 31#5) (dispatched s shape step))
    (by rw [sp, pointer]; omega)
    (by simpa only [sp, pointer, Nat.add_zero] using protected 0 (Or.inl rfl))
  have highRead := frame_read (BooleanBody.body_frame owned.bodyGeometry)
    (r (.GPR 31#5) (dispatched s shape step) + 8#64)
    (by rw [sp, nextPointer]; omega)
    (by simpa only [sp, nextPointer, show (r (.GPR 31#5) s).toNat - 16 + 8 =
      (r (.GPR 31#5) s).toNat - 8 by omega] using protected 8 (Or.inr rfl))
  rw [lowRead, highRead, sp,
    Memory.mem_eq_iff_read_mem_bytes_eq.mp (dispatched_memory s shape step),
    Memory.mem_eq_iff_read_mem_bytes_eq.mp (dispatched_memory s shape step)]
  exact entered_saved s low

def booleanFinal (s : ArmState) (shape : Desc) (step : PathStep) : ArmState :=
  returned (BooleanBody.block BooleanBody.ops (dispatched s shape step))

private theorem boolean_frame {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : Owned s shape step) :
    Delimited.MemoryFrame (writes s) s (booleanFinal s shape step) := by
  intro address outside
  have out := dispatched_register s shape step 0#5 (by decide)
  have sp := dispatched_sp s shape step
  have low := owned.stackLow
  have bound := (r (.GPR 31#5) s).isLt
  have pointer : (r (.GPR 31#5) s - 16#64).toNat =
      (r (.GPR 31#5) s).toNat - 16 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have outApart := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [writes])
  have stackApart := outside ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [writes])
  simp only [Prod.fst, Prod.snd] at outApart stackApart
  rw [booleanFinal, returned_memory]
  refine (BooleanBody.body_frame owned.bodyGeometry address ?_).trans
    (dispatched_frame owned.entry address ?_)
  · intro span member
    simp only [BooleanBody.writes, out, sp, pointer, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp only [Prod.fst, Prod.snd] <;> omega
  · intro span member
    simp only [entryWrites, List.mem_singleton] at member
    subst span
    simp only [Prod.fst, Prod.snd]
    omega

private theorem boolean_returned {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : Owned s shape step) (error : read_err s = .None) :
    Delimited.Returned s (booleanFinal s shape step) := by
  have saved := body_saved owned
  dsimp only at saved
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [booleanFinal, returned_pc, BooleanBody.body_sp] using saved.1
  · simpa only [booleanFinal, returned_error, BooleanBody.block_error,
      dispatched_error] using error
  · simp only [booleanFinal, returned_sp, BooleanBody.body_sp, dispatched_sp,
      BitVec.sub_add_cancel]
  · intro reg lower upper
    by_cases is19 : reg = 19#5
    · subst reg
      simpa only [booleanFinal, returned_x19, BooleanBody.body_sp] using saved.2
    by_cases is30 : reg = 30#5
    · subst reg
      simpa only [booleanFinal, returned_lr, BooleanBody.body_sp] using saved.1
    have bodyUntouched : reg ∉ [9#5, 10#5, 31#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl) <;> simp only [BitVec.toNat_ofNat] at lower upper <;> omega
    have dispatchUntouched : reg ∉ [8#5, 9#5, 10#5, 31#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> simp only [BitVec.toNat_ofNat] at lower upper <;> omega
    have notSP : reg ≠ 31#5 := by
      intro equal
      subst reg
      simp only [BitVec.toNat_ofNat] at upper
      omega
    rw [booleanFinal, returned_register _ reg notSP is19 is30,
      BooleanBody.block_register _ _ _ bodyUntouched,
      dispatched_register _ _ _ _ dispatchUntouched]
  · intro reg lower upper
    simp only [booleanFinal, returned_vector, BooleanBody.block_vector, dispatched_vector]

private theorem boolean_value {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : Owned s shape step) (bits : IsBitShape shape) :
    (Storage.descResult (r (.GPR 0#5) s).toNat
      (SszNative.Indices.elementType shape step)).At (booleanFinal s shape step) := by
  rw [bit_element shape step bits]
  have body := BooleanBody.body_result owned.bodyGeometry
  rw [dispatched_register s shape step 0#5 (by decide)] at body
  have initial : (Storage.descResult (r (.GPR 0#5) s).toNat
      (.ok (.primitive .bool))).Owned []
      (BooleanBody.block BooleanBody.ops (dispatched s shape step)) :=
    Codec.Storage.Image.weaken _ (by
      intro address bytes _
      right
      simp) body
  exact (Codec.Storage.Image.preserved _
    (fun address _ => congrFun (returned_memory _) address) initial).at

/-- Original-entry-through-original-return execution for the three-case bit
descriptor branch, including arbitrary raw counts and every PathStep. -/
theorem boolean_program (s : ArmState) (base : BitVec 64) (shape : Desc) (step : PathStep)
    (owned : Owned s shape step) (bits : IsBitShape shape)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run 30 s = booleanFinal s shape step ∧ Result s (booleanFinal s shape step) shape step := by
  have route := entry_dispatch_run s base shape step owned.entry code error aligned pc
  have kind := bit_destination shape step bits
  rw [kind.2] at route
  have body := BooleanBody.body_return_run (dispatched s shape step) base
    (Codec.Linked.WordsAt.preserve code (dispatched_program s shape step))
    ((dispatched_error s shape step).trans error) (dispatched_aligned s shape step aligned)
    (by simpa only [kind.1] using route.2)
  refine ⟨?_, boolean_returned owned error, boolean_value owned bits,
    boolean_frame owned, ?_⟩
  · change run (9 + 21) s = _
    rw [run_plus, route.1]
    exact body
  · simp only [booleanFinal, returned_program, BooleanBody.block_program, dispatched_program]

end SszArm.Indices.ElementType
