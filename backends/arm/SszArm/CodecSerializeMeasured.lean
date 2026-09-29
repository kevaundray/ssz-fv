import SszArm.CodecSerializeSaved

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (MemoryFrame)

structure Measured (s t : ArmState) (base : BitVec 64) (desc : Desc) (value : Value) : Prop where
  pc : read_pc t = base + 52#64
  error : read_err t = .None
  aligned : CheckSPAlignment t
  program : t.program = s.program
  registers : SszArm.Serialize.Registers t (Args.ofEntry s)
  result : Measure.ResultAt t (Args.ofEntry s).plan.toNat
    (measured s (Args.ofEntry s) desc value).result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (measured s (Args.ofEntry s) desc value).used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  effects : ∀ effect ∈ (measured s (Args.ofEntry s) desc value).effects, Measure.EffectAt t effect
  frame : MemoryFrame (SszArm.Serialize.saveWrites (Args.ofEntry s) ++
    Measure.writesFor (Args.ofEntry s).measure desc (measured s (Args.ofEntry s) desc value)) s t
  descriptor : Storage.DescAt t (Args.ofEntry s).descriptor.toNat desc
  value_at : Storage.ValueAt t (Args.ofEntry s).value.toNat value
  saved : ∀ reg displacement, (reg, displacement) ∈ SszArm.Serialize.savedRegisters →
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 displacement) t = r (.GPR reg) s
  untouched : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
    reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

/-- Internal return composition. Its helper post and frame are conclusions of
the recursive machine theorem, not assumptions in the original-entry contract. -/
theorem measured_of_return (s t : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value) (aligned : CheckSPAlignment s)
    (post : Measure.Post (SszArm.Serialize.measurementEntry base s) t desc value)
    (calleeFrame : MemoryFrame
      (Measure.envelope (SszArm.Serialize.measurementEntry base s)
        (Measure.Args.ofEntry (SszArm.Serialize.measurementEntry base s)) desc)
      (SszArm.Serialize.measurementEntry base s) t) :
    Measured s t base desc value := by
  let u := SszArm.Serialize.measurementEntry base s
  have minimum := requiredStack_min desc
  have low : 432 ≤ (r (.GPR 31#5) s).toNat := by
    have enough := owned.stackLow
    change requiredStack desc ≤ (r (.GPR 31#5) s).toNat at enough
    omega
  have entryFrame := SszArm.Serialize.measurementEntry_frame s base low
  have stackFrame := (save_covered (Args.ofEntry s) desc owned.stackLow).frame entryFrame
  have sameArena : arenaOf u (Args.ofEntry s) = arenaOf s (Args.ofEntry s) :=
    arenaOf_eq_of_stack_frame owned stackFrame
  have entryArgs : Measure.Args.ofEntry u = (Args.ofEntry s).measure :=
    SszArm.Serialize.measurementEntry_args base s
  have sameOutcome : Measure.outcome u (Measure.Args.ofEntry u) desc value =
      measured s (Args.ofEntry s) desc value := by
    rw [entryArgs]
    change SszNative.CodecMeasure.measure desc value (arenaOf u (Args.ofEntry s)) true = _
    rw [sameArena]
    rfl
  have exactFrame : MemoryFrame
      (Measure.writesFor (Args.ofEntry s).measure desc (measured s (Args.ofEntry s) desc value)) u t := by
    simpa only [sameOutcome, entryArgs] using post.frame
  have broadFrame : MemoryFrame (Measure.envelope s (Args.ofEntry s).measure desc) u t := by
    have same : Measure.envelope u (Args.ofEntry s).measure desc =
        Measure.envelope s (Args.ofEntry s).measure desc := by
      have arenaEqual : Measure.arenaOf u (Args.ofEntry s).measure =
          Measure.arenaOf s (Args.ofEntry s).measure := sameArena
      simp only [Measure.envelope, arenaEqual]
    simpa only [entryArgs, same] using calleeFrame
  have registers : SszArm.Serialize.Registers t (Args.ofEntry s) := by
    have before := SszArm.Serialize.measurementEntry_registers base s
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (post.returned.registers 19#5 (by decide) (by decide)).trans before.result
    · exact (post.returned.registers 20#5 (by decide) (by decide)).trans before.output
    · exact (post.returned.registers 21#5 (by decide) (by decide)).trans before.value
    · exact (post.returned.registers 22#5 (by decide) (by decide)).trans before.descriptor
    · exact (post.returned.registers 23#5 (by decide) (by decide)).trans before.capacity
    · exact post.returned.sp.trans before.stack
  refine ⟨post.returned.pc.trans (SszArm.Serialize.measurementEntry_lr base s),
    post.returned.error, ?_, post.program.trans (SszArm.Serialize.measurementEntry_program base s),
    registers, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CheckSPAlignment_of_r_sp_aligned post.returned.sp
      (BoolCodec.stack_aligned u (SszArm.Serialize.measurementEntry_aligned base s aligned))
  · simpa only [sameOutcome, entryArgs, SszArm.Serialize.Args.measure] using post.result
  · simpa only [sameOutcome, entryArgs, SszArm.Serialize.Args.measure] using post.cursor
  · have header := post.header
    simp only [entryArgs, SszArm.Serialize.Args.measure] at header
    have baseRead : read_mem_bytes 8 (Args.ofEntry s).arena u =
        read_mem_bytes 8 (Args.ofEntry s).arena s := by
      apply BitVec.eq_of_toNat_eq
      exact congrArg SszNative.Delimited.ArenaState.base sameArena
    have capacityRead : read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) u =
        read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s := by
      apply BitVec.eq_of_toNat_eq
      exact congrArg SszNative.Delimited.ArenaState.capacity sameArena
    exact ⟨header.1.trans baseRead, header.2.trans capacityRead⟩
  · simpa only [sameOutcome] using post.effects
  · exact (entryFrame.weaken (fun _ member => List.mem_append.mpr (Or.inl member))).trans
      (exactFrame.weaken (fun _ member => List.mem_append.mpr (Or.inr member)))
  · simpa only [entryArgs, SszArm.Serialize.Args.measure] using post.descriptor
  · simpa only [entryArgs, SszArm.Serialize.Args.measure] using post.value_at
  · intro reg displacement member
    have range : 96 ≤ displacement ∧ displacement + 8 ≤ 144 := by
      apply SszArm.Serialize.Finish.saved_bounds reg displacement
      exact member
    rw [measure_saved_read owned broadFrame displacement range.1 range.2]
    exact SszArm.Serialize.measurementEntry_saved s base low reg displacement member
  · intro reg lower upper untouched
    exact (post.returned.registers reg lower (by omega)).trans
      (SszArm.Serialize.measurementEntry_untouched base s reg (by omega) upper untouched)
  · intro reg lower upper
    rw [post.returned.vectors reg lower upper, SszArm.Serialize.measurementEntry_vector]

end SszArm.Codec.Serialize
