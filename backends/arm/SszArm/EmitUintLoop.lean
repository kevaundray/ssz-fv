import SszArm.EmitUintLoopEntry

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)

theorem prefix_bytes (s : ArmState) (args : Args) (number : NatOperand) (size : Nat)
    (writtenPrefix : Prefix s args number size) :
    SszNative.ByteView.BytesAt (widthLoad s) args.output.toNat (SszNative.Limbs.bytes number.words size) := by
  intro index inside
  have bound : index < size := by simpa only [SszNative.Limbs.bytes, Array.size_ofFn] using inside
  rw [emitted_array_byte number size index bound]
  exact writtenPrefix index bound

/-- Actual PC916 pair load and representation dispatch, followed by either
zero-extended Small or arbitrarily padded Large byte iteration. This theorem
stops before the actual common length store, with the entire prefix initialized. -/
theorem loop_to_result (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : NatOperand) (size : Nat)
    (code : CodeAt s base) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 916#64) (length : r (.GPR 1#5) s = BitVec.ofNat 64 size)
    (positive : 0 < size) :
    ∃ steps t, run steps s = t ∧ Frame s t args size ∧ read_pc t = base + 1000#64 ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size ∧
      SszNative.ByteView.BytesAt (widthLoad t) args.output.toNat
        (SszNative.Serialize.emit (.uint width) (.uint number)) := by
  have entryRun := number_entry_run base owned registers code error aligned pc
  have entryFrame := numberEntered_frame s base number args size
  have entryOwned := entryFrame.owned owned
  have entryRegisters := entryFrame.bodyRegisters registers
  have entryCode := entryFrame.code code
  have entryError := entryFrame.error.trans error
  have entryAligned := entryFrame.aligned aligned
  have widthEq := expected_width owned
  cases number with
  | small word =>
    obtain ⟨entryPC, loop⟩ := numberEntered_small s base word size length
    obtain ⟨steps, t, loopRun, loopFrame, finalPC, finalLength, writtenPrefix⟩ :=
      small_loop size (numberEntered s base (.small word)) base args width word size 0
        entryOwned entryRegisters entryCode entryError entryAligned entryPC loop
        (by intro index impossible; omega) (by omega) positive
    refine ⟨(numberEntryOps (.small word)).length + steps, t, ?_, entryFrame.trans loopFrame,
      finalPC, finalLength, ?_⟩
    · rw [run_plus, entryRun, loopRun]
    · simpa only [SszNative.Serialize.emit, widthEq] using prefix_bytes t args (.small word) size writtenPrefix
  | large pointer words =>
    obtain ⟨entryPC, loop⟩ := numberEntered_large s base pointer words size length
    obtain ⟨steps, t, loopRun, loopFrame, finalPC, finalLength, writtenPrefix⟩ :=
      large_loop size (numberEntered s base (.large pointer words)) base args width pointer words size 0
        entryOwned entryRegisters entryCode entryError entryAligned entryPC loop
        (by intro index impossible; omega) (by omega) positive
    refine ⟨(numberEntryOps (.large pointer words)).length + steps, t, ?_, entryFrame.trans loopFrame,
      finalPC, finalLength, ?_⟩
    · rw [run_plus, entryRun, loopRun]
    · simpa only [SszNative.Serialize.emit, widthEq] using prefix_bytes t args (.large pointer words) size writtenPrefix

end SszArm.Emit.Uint
