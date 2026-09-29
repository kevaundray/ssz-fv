import SszArm.CodecSerializeGeometry

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (Protected MemoryFrame)

 theorem Owned.measure {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (aligned : args.stack.toNat % 16 = 0) :
    Measure.Owned s args.measure desc value := by
  have minimum := requiredStack_min desc
  have localCover := measure_local_covered args desc owned.stackLow
  refine ⟨Or.inr rfl, plan_physical args desc owned.stackLow aligned, owned.arena,
    owned.storageBound, owned.nonnull, ?_, measure_result_stack args desc owned.stackLow,
    ?_, ?_, owned.measure_descriptor, owned.measure_value⟩
  · change Measure.stackBytes desc ≤ args.bodySP.toNat
    rw [SszArm.Serialize.bodySP_toNat args (by have := owned.stackLow; omega)]
    exact measure_stack_low owned.stackLow
  · apply BitVector.Covers.protected (owned := owned.arenaOwned)
    intro span member
    obtain ⟨outer, included, lower, upper⟩ := localCover span member
    exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩
  · apply BitVector.Covers.protected (owned := owned.freeOwned)
    intro span member
    rcases List.mem_append.mp member with localMember | header
    · obtain ⟨outer, included, lower, upper⟩ := localCover span localMember
      exact ⟨outer, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl included))),
        lower, upper⟩
    · exact ⟨span, List.mem_append.mpr (Or.inr header), Nat.le_refl _, Nat.le_refl _⟩

 theorem arenaOf_eq_of_stack_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (stackSpans args desc) s t) :
    arenaOf t args = arenaOf s args := by
  have separated : Protected (stackSpans args desc) args.arena.toNat 24 := by
    apply BitVector.Covers.protected (owned := owned.arenaOwned)
    intro span member
    exact ⟨span, List.mem_append.mpr (Or.inl member), Nat.le_refl _, Nat.le_refl _⟩
  have bound := owned.arena.2.2.1
  have header := SszArm.Emit.frame_read_offset frame args.arena 24 0 8 bound separated (by decide)
  have capacity := SszArm.Emit.frame_read_offset frame args.arena 24 8 8 bound separated (by decide)
  have cursor := SszArm.Emit.frame_read_offset frame args.arena 24 16 8 bound separated (by decide)
  simp only [BitVec.add_zero] at header
  simp only [arenaOf, Measure.arenaOf, SszArm.Measure.arenaOf,
    SszArm.Serialize.Args.measure, header, capacity, cursor]

 theorem Owned.of_stack_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (stackSpans args desc) s t) :
    Owned t args desc value := by
  have same := arenaOf_eq_of_stack_frame owned frame
  have free : freeSpan t args = freeSpan s args := by simp only [freeSpan, same]
  have sameEnvelope : envelope t args desc = envelope s args desc := by simp only [envelope, free]
  have wideFrame : MemoryFrame (envelope s args desc) s t := by
    apply frame.weaken
    intro span member
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))
  refine { owned with
    storageBound := ?_
    nonnull := ?_
    freeOwned := ?_
    descriptor := ?_
    value_at := ?_ }
  · simpa only [same] using owned.storageBound
  · simpa only [same] using owned.nonnull
  · simpa only [free] using owned.freeOwned
  · rw [sameEnvelope]
    exact Storage.desc_preserved owned.descriptor wideFrame
  · rw [sameEnvelope]
    exact Storage.value_preserved owned.value_at wideFrame

/-- Callee storage is derived at the real BL destination from original wrapper
ownership and executed prologue stores; it is not supplied as a future premise. -/
theorem measurement_owned (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value) (aligned : CheckSPAlignment s) :
    Measure.Owned (SszArm.Serialize.measurementEntry base s)
      (Measure.Args.ofEntry (SszArm.Serialize.measurementEntry base s)) desc value := by
  have minimum := requiredStack_min desc
  have low : 432 ≤ (r (.GPR 31#5) s).toNat := by
    have enough := owned.stackLow
    change requiredStack desc ≤ (r (.GPR 31#5) s).toNat at enough
    omega
  have frame := (save_covered (Args.ofEntry s) desc owned.stackLow).frame
    (SszArm.Serialize.measurementEntry_frame s base low)
  have savedOwned := owned.of_stack_frame frame
  have wordAligned := BoolCodec.stack_aligned s aligned
  have naturalAligned : (Args.ofEntry s).stack.toNat % 16 = 0 := by
    change (r (.GPR 31#5) s).toNat % 16 = 0
    simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at wordAligned
    bv_omega
  have initial := savedOwned.measure naturalAligned
  simpa only [Measure.Args.ofEntry, SszArm.Serialize.measurementEntry_args] using initial

end SszArm.Codec.Serialize
