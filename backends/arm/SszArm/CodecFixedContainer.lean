import SszArm.CodecFixedFieldsLoop
import SszArm.CodecFixedFieldsSetup
import SszArm.CodecFixedFinish

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

theorem container_body_correct (progressive : Bool) (active : List Bool)
    (fields : List (String × Desc)) (children : ∀ field ∈ fields, BodyCorrect field.2) :
    BodyCorrect (if progressive then .progressiveContainer active fields else .container fields) := by
  intro source current base owned code error aligned pc loaded
  let desc : Desc := if progressive then .progressiveContainer active fields else .container fields
  let budget := max 16 (isFixedFieldsStack fields)
  let offset : Nat := if progressive then 24 else 8
  have stackEq : isFixedStack desc = 32 + budget := by cases progressive <;> rfl
  have writesEq : writes source desc = fieldWrites source budget := by
    simp only [writes, fieldWrites, stackEq]
  have input : Storage.DescOwned (fieldWrites source budget) current (r (.GPR 0#5) current).toNat desc := by
    rw [← writesEq]
    exact owned.descriptor
  have payload : ∃ pointer,
      (Storage.Image.word ((r (.GPR 0#5) current).toNat + offset) 8 pointer).Owned
        (fieldWrites source budget) current ∧
      (Storage.Image.word ((r (.GPR 0#5) current).toNat + offset + 8) 8 fields.length).Owned
        (fieldWrites source budget) current ∧
      Storage.Physical pointer (fields.length * 24) 8 ∧
      (Storage.fieldEntries pointer fields).Owned (fieldWrites source budget) current := by
    cases progressive with
    | false =>
      simpa only [offset, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using Storage.container_fields input
    | true =>
      simpa only [offset, ↓reduceIte, Nat.add_assoc] using Storage.progressiveContainer_fields input
  obtain ⟨pointer, pointerAt, countAt, physical, fieldInput⟩ := payload
  have countBound : 24 * fields.length < 2^64 := by
    have small := physical.2.2.2
    simp only [Nat.mul_comm] at small
    omega
  have pointerRead : read_mem_bytes 8 (r (.GPR 0#5) current + fieldsOffset progressive) current =
      BitVec.ofNat 64 pointer := by
    have observed := congrArg (BitVec.ofNat 64)
      (Storage.word_offset (r (.GPR 0#5) current) offset pointerAt)
    cases progressive <;>
      simpa only [offset, fieldsOffset, Bool.false_eq_true, ↓reduceIte,
        BitVec.ofNat_toNat, BitVec.setWidth_eq] using observed
  have countRead : read_mem_bytes 8 (r (.GPR 0#5) current + fieldsOffset progressive + 8#64) current =
      BitVec.ofNat 64 fields.length := by
    have observed := congrArg (BitVec.ofNat 64)
      (Storage.word_offset (r (.GPR 0#5) current) (offset + 8) (by
        simpa only [Nat.add_assoc] using countAt))
    cases progressive <;>
      simpa only [offset, fieldsOffset, Bool.false_eq_true, ↓reduceIte,
        BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add, BitVec.add_assoc] using observed
  let d := block (selectedOps desc.tag) current
  have dRun : run (selectedOps desc.tag).length current = d := selected_run current base desc.tag code error aligned pc loaded
  have dPC : read_pc d = base + if progressive then 80#64 else 88#64 := by
    have selected := selected_pc current base desc.tag pc loaded
    cases progressive <;> exact selected
  have dCode : CodeAt d base := by simpa only [CodeAt, d, block_program] using code
  have dError : read_err d = .None := (block_error _ current).trans error
  have dAligned : CheckSPAlignment d := block_aligned _ current aligned
  have dPointer : read_mem_bytes 8 (r (.GPR 0#5) d + fieldsOffset progressive) d = BitVec.ofNat 64 pointer := by
    rw [selected_register current desc.tag 0#5,
      (Memory.mem_eq_iff_read_mem_bytes_eq.mp (selected_memory current desc.tag))]
    exact pointerRead
  have dCount : read_mem_bytes 8 (r (.GPR 0#5) d + fieldsOffset progressive + 8#64) d =
      BitVec.ofNat 64 fields.length := by
    rw [selected_register current desc.tag 0#5,
      (Memory.mem_eq_iff_read_mem_bytes_eq.mp (selected_memory current desc.tag))]
    exact countRead
  let q := block (fieldsSetupOps progressive) d
  have setupRun : run (fieldsSetupOps progressive).length d = q :=
    fields_setup_run d base progressive dCode dError dAligned dPC
  have setupArgs := fields_setup_arguments d progressive (BitVec.ofNat 64 pointer)
    fields.length countBound dPointer dCount
  have setupFrame : Delimited.MemoryFrame (fieldWrites source budget) current q := by
    intro address outside
    rw [show q.mem = d.mem from fields_setup_memory d progressive,
      show d.mem = current.mem from selected_memory current desc.tag]
  have qOwned : FieldsOwned source q fields pointer budget := by
    refine ⟨?_, Nat.le_max_left _ _, Nat.le_max_right _ _,
      (owned.context.selected desc.tag).fields_setup progressive, setupArgs.1, setupArgs.2,
      ?_, countBound, Storage.Image.preserved _ setupFrame fieldInput⟩
    · simpa only [stackEq] using owned.stack
    · simpa only [Nat.mul_comm] using physical.2.2.1
  have qCode : CodeAt q base := by simpa only [CodeAt, q, block_program] using dCode
  have qError : read_err q = .None := (block_error _ d).trans dError
  have qAligned : CheckSPAlignment q := block_aligned _ d dAligned
  have qPC : read_pc q = base + 108#64 := fields_setup_pc d base progressive dPC
  obtain ⟨loopFuel, z, loopRun, loopPost⟩ := fields_loop source base budget fields pointer q
    qOwned children qCode qError qAligned qPC
  have zCode : CodeAt z base := by simpa only [CodeAt, loopPost.program] using qCode
  have zSP : r (.GPR 31#5) z = r (.GPR 31#5) q :=
    loopPost.context.saved.sp.trans qOwned.context.saved.sp.symm
  have zAligned : CheckSPAlignment z := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, zSP] using qAligned
  have zPC : read_pc z = base + if SszNative.FixedSize.isFixed desc then 188#64 else 172#64 := by
    cases progressive <;> exact loopPost.pc
  obtain ⟨final, finishRun, finishPost⟩ := finish_body source z base desc loopPost.context zCode loopPost.error zAligned zPC
  refine ⟨(selectedOps desc.tag).length + (fieldsSetupOps progressive).length + loopFuel + 4,
    final, ?_, finishPost.returned, finishPost.platform, ?_, finishPost.result, ?_⟩
  · rw [run_plus, run_plus, run_plus, dRun, setupRun, loopRun, finishRun]
  · exact finishPost.program.trans (loopPost.program.trans
      ((block_program _ d).trans (block_program _ current)))
  · have throughLoop : Delimited.MemoryFrame (writes source desc) current z := by
      rw [writesEq]
      exact setupFrame.trans loopPost.frame
    exact throughLoop.trans finishPost.frame

end SszArm.Codec.Fixed.IsFixed
