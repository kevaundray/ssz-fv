import SszX86.BitVectorFinishExactOwned
import SszX86.BitVectorFinish
import SszX86.BitVectorErrorsReads

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The actual exact setup, linked call, status branch and complete terminal suffix.
Every premise describes the reached physical world or derived division arithmetic;
no future helper outcome, native guard or return transition is assumed. -/
theorem finish_exact_suffix_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length expected : NatOperand) (data : Ssz.Bytes)
    (remainder address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (remainderReg : u.regs.r13.toBitVec = remainder)
    (metadata : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 208) expected)
    (protectedOperand : OperandProtected s address capacity currentUsed expected)
    (arithmetic : SszNative.BitVector.Expected length expected remainder) :
    Eventually (step e)
      (Terminal s saved u.dmem data (SszNative.BitVector.finish length expected remainder data))
      (u, base + 4618) := by
  let actual := BitVec.ofNat 64 data.size
  have physical : data.size < 2^64 := by
    rw [world.physical.data_length]
    exact s.regs.r14.toBitVec.isLt
  have actualValue : actual.toNat = data.size := Nat.mod_eq_of_lt physical
  have actualRegister : u.regs.r14.toBitVec = actual := by
    rw [anchors.count]
    dsimp only [actual]
    rw [world.physical.data_length]
    change s.regs.r14.toBitVec = BitVec.ofNat 64 s.regs.r14.toBitVec.toNat
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have helper := finish_exact_owned s u saved length expected data address capacity currentUsed
    actual (base + 4639).toBitVec world.physical anchors.stack actualRegister metadata protectedOperand
  have slot := finish_exact_slot s (exactSetupState u) saved length data address capacity currentUsed
    world.physical anchors.stack
  apply exact_setup_cps e base hc.body u
  apply exact_cps e base hc (exactSetupState u) expected actual slot helper
  intro t post
  have frame := finish_exact_frame s u expected actual (base + 4639).toBitVec anchors.stack low high t post
  have workFrame := finish_exact_work s u.dmem t.1.dmem low frame
  have finalFrame : RegionsFrame u.dmem t.1.dmem (finishRegions s) := by
    apply workFrame.weaken
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp [finishRegions]
  have worldAfter := world.local workFrame (finish_exact_mapping u expected actual _ t post)
  have anchorsAfter := finish_exact_anchors s u length expected actual _ anchors high t post frame
  have remainderAfter : t.1.regs.r13.toBitVec = remainder := by
    rw [post.returned.r13]
    exact remainderReg
  have pc : t.2 = base + 4639 := by simpa only [Int64.ofBitVec_toBitVec] using post.returned.pc
  have helperOutput : (callState (exactSetupState u) (base + 4639).toBitVec).regs.rdi.toNat =
      s.regs.rsp.toNat + 16 := by
    change (u.regs.rsp.toBitVec + 16#64).toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [anchors.stack]
    have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
    bv_omega
  have observed : NatNarrow.ExactResultAt (widthLoad t.1.dmem)
      (t.1.regs.rsp.toNat + 16) expected actual := by
    simpa only [helperOutput, anchorsAfter.stack] using post.observed
  change Eventually (step e) _ (t.1, t.2)
  rw [pc]
  apply eventually_trans (step e)
    (Terminal s saved t.1.dmem data (SszNative.BitVector.finish length expected remainder data)) _ _
  · cases checked : NatNarrow.runExact expected (BitVec.ofNat 64 data.size) with
    | false =>
      have failedObserved := observed
      simp only [NatNarrow.ExactResultAt, actual, checked, Bool.false_eq_true, ↓reduceIte]
        at failedObserved
      have statusRead : Mem.loadInt t.1.dmem (t.1.regs.rsp.toBitVec + 80#64) 4 =
          some ((3#32).toNat : Int) := by
        simp only [show (3#32).toNat = 3 by decide]
        errors_private_read 80 from failedObserved.2.2.2.2.2.2.2
      apply exact_status_cps e base hc.body t.1 3#32 statusRead
      intro flags
      simp only [show (3#32 : BitVec 32) ≠ 0#32 by decide, ↓reduceIte,
        SszNative.BitVector.finish, checked, Bool.false_eq_true]
      let v := {t.1 with status := flags}
      have privateMapped : Large.Mapped v.dmem (v.regs.rsp.toBitVec + 16#64) 72 := by
        have part := mapped_subrange t.1.dmem (s.regs.rsp.toBitVec - 72#64) workSize 88 72
          worldAfter.physical.work_mapped (by decide)
        simpa only [v, anchorsAfter.stack,
          show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 88 = s.regs.rsp.toBitVec + 16#64
            by bv_omega] using part
      obtain ⟨padding, inputReads⟩ := exact_reads_of_private v expected actual observed checked privateMapped
      have reached : ErrorSuffixAt s v saved := by
        refine ⟨original, anchorsAfter.stack, worldAfter.physical.saved_at,
          worldAfter.physical.output_bound, worldAfter.physical.output_mapped, low, high,
          worldAfter.physical.output_work, worldAfter.physical.output_saved, ?_⟩
        simpa only [v, anchorsAfter.stack] using anchorsAfter.outputCache
      apply exact_error_terminal e base hc.body s v saved data expected actual padding reached inputReads
        actualValue (finish_exact_slot s v saved length data address capacity currentUsed
          worldAfter.physical anchorsAfter.stack)
      intro pointer limbs equal
      subst expected
      exact ⟨protectedOperand.output, protectedOperand.work⟩
    | true =>
      have passedObserved := observed
      simp only [NatNarrow.ExactResultAt, actual, checked, ↓reduceIte] at passedObserved
      have statusRead : Mem.loadInt t.1.dmem (t.1.regs.rsp.toBitVec + 80#64) 4 =
          some ((0#32).toNat : Int) := by
        simp only [show (0#32).toNat = 0 by decide]
        errors_private_read 80 from passedObserved
      apply exact_status_cps e base hc.body t.1 0#32 statusRead
      intro flags
      simp only [↓reduceIte]
      exact finish_suffix_correct e base hc s {t.1 with status := flags} saved length expected
        remainder address capacity currentUsed data worldAfter.physical original anchorsAfter.stack
        anchorsAfter.count remainderAfter anchorsAfter.pointer anchorsAfter.payload
        anchorsAfter.outputCache anchorsAfter.sourceCache arithmetic checked
  · intro z terminal
    exact Eventually.done _ ⟨terminal.observed, terminal.returned,
      finish_frame_trans finalFrame terminal.frame⟩

end SszX86.BitVector
