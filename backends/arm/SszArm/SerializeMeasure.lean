import SszArm.SerializeEntry
import SszArm.SerializeOwnership
import SszArm.MeasureProgram

namespace SszArm.Serialize

open SszNative.Serialize (Desc Value)
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

structure Measured (s t : ArmState) (base : BitVec 64) (desc : Desc) (value : Value) : Prop where
  pc : read_pc t = base + 52#64
  code : CodeAt t base
  error : read_err t = .None
  aligned : CheckSPAlignment t
  registers : Registers t (Args.ofEntry s)
  program : t.program = s.program
  result : Measure.ResultAt (widthLoad t) (Args.ofEntry s).plan.toNat
    (measured s (Args.ofEntry s) desc value).result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (measured s (Args.ofEntry s) desc value).used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  written : ∀ call ∈ (measured s (Args.ofEntry s) desc value).calls,
    NatDivision.WrittenAt (widthLoad t) call
  frame : MemoryFrame (saveWrites (Args.ofEntry s) ++
    Measure.writesFor (Args.ofEntry s).measure (measured s (Args.ofEntry s) desc value)) s t
  descriptor : Emit.DescriptorAt t (Args.ofEntry s).descriptor desc
  value_at : Emit.ValueAt t (Args.ofEntry s).value value
  saved : ∀ reg displacement, (reg, displacement) ∈ savedRegisters →
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 displacement) t = r (.GPR reg) s
  untouched : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 29 →
    reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

theorem measurement_correct (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Measured s t base desc value := by
  let u := measurementEntry base s
  have entryFrame := measurementEntry_frame s base owned.stackLow
  have initialOwned : Measure.Owned u (Args.ofEntry s).measure desc value :=
    owned.measure_of_save_frame entryFrame
  have calleeOwned : Measure.Owned u (Measure.Args.ofEntry u) desc value := by
    simpa only [u, measurementEntry_args] using initialOwned
  have sameArena : arenaOf u (Args.ofEntry s) = arenaOf s (Args.ofEntry s) :=
    arenaOf_eq_of_save_frame owned entryFrame
  have sameOutcome : Measure.outcome u (Measure.Args.ofEntry u) desc value =
      measured s (Args.ofEntry s) desc value := by
    rw [show Measure.Args.ofEntry u = (Args.ofEntry s).measure from measurementEntry_args base s]
    change SszNative.Serialize.measure desc value (arenaOf u (Args.ofEntry s)) = _
    rw [sameArena]
    rfl
  have entryArgs : Measure.Args.ofEntry u = (Args.ofEntry s).measure :=
    measurementEntry_args base s
  have explicitOutcome : Measure.outcome u (Args.ofEntry s).measure desc value =
      measured s (Args.ofEntry s) desc value := by
    rw [← entryArgs]
    exact sameOutcome
  have ucode : CodeAt u base := code.congr (measurementEntry_program base s)
  obtain ⟨fuel, t, executed, post⟩ := Measure.program_correct u (base + measureOffset) desc value
    calleeOwned ucode.measure ((measurementEntry_error base s).trans error)
    (measurementEntry_aligned base s aligned) (measurementEntry_pc base s)
  have calleeFrame : MemoryFrame
      (Measure.writesFor (Args.ofEntry s).measure (measured s (Args.ofEntry s) desc value)) u t := by
    simpa only [entryArgs, explicitOutcome] using post.frame
  have registers : Registers t (Args.ofEntry s) := by
    have before := measurementEntry_registers base s
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (post.returned.registers 19#5 (by decide) (by decide)).trans before.result
    · exact (post.returned.registers 20#5 (by decide) (by decide)).trans before.output
    · exact (post.returned.registers 21#5 (by decide) (by decide)).trans before.value
    · exact (post.returned.registers 22#5 (by decide) (by decide)).trans before.descriptor
    · exact (post.returned.registers 23#5 (by decide) (by decide)).trans before.capacity
    · exact post.returned.sp.trans before.stack
  have sameProgram : t.program = s.program :=
    post.returned.program.trans (measurementEntry_program base s)
  refine ⟨13 + fuel, t, ?_, ?_⟩
  · rw [run_plus, measurementEntry_run s base code error aligned pc]
    exact executed
  · refine ⟨?_, code.congr sameProgram, post.returned.error, ?_, registers, sameProgram,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact post.returned.pc.trans (measurementEntry_lr base s)
    · exact CheckSPAlignment_of_r_sp_aligned post.returned.sp
        (BoolCodec.stack_aligned u (measurementEntry_aligned base s aligned))
    · have observed := post.result
      rw [sameOutcome] at observed
      simpa only [entryArgs, Args.measure] using observed
    · have cursor := post.cursor
      rw [sameOutcome] at cursor
      simpa only [entryArgs, Args.measure] using cursor
    · have header0 := Emit.frame_read_offset entryFrame (Args.ofEntry s).arena 24 0 8
        owned.arenaBound (protected_of_covers owned.arenaOwned (by
          intro span member
          obtain ⟨outer, outerMember, lower, upper⟩ := save_covered (Args.ofEntry s) span member
          exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩)) (by decide)
      have header8 := Emit.frame_read_offset entryFrame (Args.ofEntry s).arena 24 8 8
        owned.arenaBound (protected_of_covers owned.arenaOwned (by
          intro span member
          obtain ⟨outer, outerMember, lower, upper⟩ := save_covered (Args.ofEntry s) span member
          exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩)) (by decide)
      have prior := post.header
      simp only [u, measurementEntry_args, Args.measure] at prior
      simp only [BitVec.add_zero] at header0
      exact ⟨prior.1.trans header0, prior.2.trans header8⟩
    · simpa only [sameOutcome] using post.written
    · exact (entryFrame.weaken (fun _ member => List.mem_append.mpr (Or.inl member))).trans
        (calleeFrame.weaken (fun _ member => List.mem_append.mpr (Or.inr member)))
    · simpa only [u, measurementEntry_args, Args.measure] using post.descriptor
    · simpa only [u, measurementEntry_args, Args.measure] using post.value_at
    · intro reg displacement member
      have range : 96 ≤ displacement ∧ displacement + 8 ≤ 144 := by
        simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      have address : ((Args.ofEntry s).bodySP + BitVec.ofNat 64 displacement).toNat =
          (Args.ofEntry s).stack.toNat - 144 + displacement := by
        have bound := (Args.ofEntry s).stack.isLt
        have low := owned.stackLow
        simp only [Args.bodySP]
        bv_omega
      have protectedRead : Delimited.Protected
          (Measure.writesFor (Args.ofEntry s).measure (measured s (Args.ofEntry s) desc value))
          ((Args.ofEntry s).bodySP + BitVec.ofNat 64 displacement).toNat 8 := by
        have protectedSave := saved_protected_measure owned
        have subset := protectedSave.subspan (displacement - 96) 8 (by omega)
        rw [address]
        have low := owned.stackLow
        have offsetEq : (Args.ofEntry s).stack.toNat - 48 + (displacement - 96) =
            (Args.ofEntry s).stack.toNat - 144 + displacement := by omega
        simpa only [offsetEq] using subset
      rw [calleeFrame.read _ 8 (by rw [address]; have := (Args.ofEntry s).stack.isLt; omega) protectedRead]
      exact measurementEntry_saved s base owned.stackLow reg displacement member
    · intro reg low high outside
      exact (post.returned.registers reg low (by omega)).trans
        (measurementEntry_untouched base s reg low high outside)
    · intro reg low high
      rw [post.returned.vectors reg low high, measurementEntry_vector]

end SszArm.Serialize
