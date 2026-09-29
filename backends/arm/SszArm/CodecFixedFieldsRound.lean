import SszArm.CodecFixedFieldsContract

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

theorem fields_round (source current : ArmState) (base : BitVec 64)
    (name : String) (child : Desc) (rest : List (String × Desc)) (pointer budget : Nat)
    (owned : FieldsOwned source current ((name, child) :: rest) pointer budget)
    (childCorrect : BodyCorrect child) (code : CodeAt current base)
    (error : read_err current = .None) (aligned : CheckSPAlignment current)
    (pc : read_pc current = base + 108#64) :
    ∃ fuel next, run fuel current = next ∧
      FieldsOwned source next rest (pointer + 24) budget ∧
      next.program = current.program ∧ read_err next = .None ∧
      read_pc next = base + if SszNative.FixedSize.isFixed child then 108#64 else 172#64 ∧
      Delimited.MemoryFrame (fieldWrites source budget) current next := by
  have childBudget : isFixedStack child ≤ budget :=
    (isFixedFieldsStack_head name child rest).trans owned.children
  have callLow : 32 + isFixedStack child ≤ (r (.GPR 31#5) source).toNat := by omega
  have bodyLow : 32 ≤ (r (.GPR 31#5) source).toNat := by have := owned.stack; omega
  have bodyNat : (r (.GPR 31#5) current).toNat = (r (.GPR 31#5) source).toNat - 32 := by
    rw [owned.context.saved.sp]
    exact Stack.sub_toNat _ 32 bodyLow
  have nonempty : r (.GPR 19#5) current ≠ 0#64 := by
    have bounded := owned.countBound
    rw [owned.count]
    simp only [List.length_cons] at bounded ⊢
    bv_omega
  obtain ⟨childPointer, pointerAt, childInput⟩ := Storage.field_child owned.fields
  have childRange := (Storage.desc_physical childInput.at).2.2.1
  have childSmall : childPointer < 2^64 := by omega
  have childPointerNat : (BitVec.ofNat 64 childPointer).toNat = childPointer := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt childSmall]
  have pointerRead := congrArg (BitVec.ofNat 64) (Storage.word_read pointerAt)
  have childRead : read_mem_bytes 8 (r (.GPR 8#5) current + 16#64) current =
      BitVec.ofNat 64 childPointer := by
    simpa only [owned.pointer, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using pointerRead
  let call := block fieldCallOps current
  have prepared := field_call_arguments current base pc nonempty
  have callRun : run 4 current = call := field_call_run current base code error aligned pc nonempty
  have callFrame : Delimited.MemoryFrame (fieldWrites source budget) current call := by
    intro address outside
    rw [show call.mem = current.mem from field_call_memory current]
  have keptChild : Storage.DescOwned (fieldWrites source budget) call childPointer child :=
    Storage.desc_preserved childInput callFrame
  have callSP : (r (.GPR 31#5) call).toNat = (r (.GPR 31#5) source).toNat - 32 := by
    rw [prepared.2.2.2.2.2]
    exact bodyNat
  have cover : BitVector.Covers (fieldWrites source budget) (writes call child) := by
    simpa only [fieldWrites, writes, callSP] using
      Stack.child_cover owned.stack (show 32 + isFixedStack child ≤ 32 + budget by omega)
  have callOwned : Owned call child := by
    refine ⟨?_, ?_⟩
    · rw [callSP]
      omega
    · rw [prepared.2.1, childRead, childPointerNat]
      exact (Storage.desc childPointer child).weaken (fun _ _ protected => cover.protected protected) keptChild
  have callCode : CodeAt call base := by simpa only [CodeAt, call, block_program] using code
  have callError : read_err call = .None := (block_error _ current).trans error
  have callAligned : CheckSPAlignment call := block_aligned _ current aligned
  obtain ⟨childFuel, returned, childRun, childPost⟩ :=
    entry_of_body child childCorrect call base callOwned callCode callError callAligned prepared.1
  have returnedContext := (owned.context.field_call).after_call callLow childPost
  have childFrame := callFrame.trans (cover.frame childPost.frame)
  have returnedPC : read_pc returned = base + 124#64 := childPost.returned.pc.trans prepared.2.2.2.2.1
  have returnedCode : CodeAt returned base := by
    simpa only [CodeAt, childPost.program] using callCode
  have returnedAligned : CheckSPAlignment returned := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, childPost.returned.sp] using callAligned
  let result := SszNative.FixedSize.isFixed child
  let next := fieldTail returned result
  have tailRun : run 9 returned = next := field_tail_run returned base result returnedCode
    childPost.returned.error returnedAligned returnedPC childPost.result
  have enough : 48 ≤ (r (.GPR 31#5) source).toNat := by
    have := owned.stack
    have := owned.lowering
    omega
  have returnedSP : (r (.GPR 31#5) returned).toNat = (r (.GPR 31#5) source).toNat - 32 := by
    rw [childPost.returned.sp]
    exact callSP
  have tailLow : 16 ≤ (r (.GPR 31#5) returned).toNat := by rw [returnedSP]; omega
  have tailCover : BitVector.Covers (fieldWrites source budget)
      (Stack.envelope (r (.GPR 31#5) returned).toNat 16) := by
    simpa only [fieldWrites, returnedSP] using
      Stack.child_cover owned.stack (show 32 + 16 ≤ 32 + budget by have := owned.lowering; omega)
  have wholeFrame := childFrame.trans (tailCover.frame (field_tail_frame returned result tailLow))
  have keptFields := Storage.Image.preserved _ wholeFrame owned.fields
  have nextArguments := field_tail_arguments returned result
  have nextPointer : r (.GPR 8#5) next = BitVec.ofNat 64 (pointer + 24) := by
    rw [nextArguments.1, childPost.returned.registers 20#5 (by decide) (by decide),
      prepared.2.2.2.1, owned.pointer, BitVec.ofNat_add]
    rfl
  have nextCount : r (.GPR 19#5) next = BitVec.ofNat 64 (24 * rest.length) := by
    rw [nextArguments.2.1, childPost.returned.registers 19#5 (by decide) (by decide),
      prepared.2.2.1, owned.count]
    simp only [List.length_cons]
    bv_omega
  refine ⟨4 + childFuel + 9, next, ?_, ?_, ?_, ?_, ?_, wholeFrame⟩
  · rw [run_plus, run_plus, callRun, childRun, tailRun]
  · refine ⟨owned.stack, owned.lowering,
      (isFixedFieldsStack_tail name child rest).trans owned.children,
      returnedContext.field_tail enough result, nextPointer, nextCount, ?_, ?_, keptFields.2⟩
    · have bounded := owned.range
      simp only [List.length_cons] at bounded
      omega
    · have bounded := owned.countBound
      simp only [List.length_cons] at bounded
      omega
  · exact (block_program (fieldTailOps result) returned).trans
      (childPost.program.trans (block_program fieldCallOps current))
  · exact (block_error (fieldTailOps result) returned).trans childPost.returned.error
  · exact field_tail_pc returned base result returnedPC childPost.result

end SszArm.Codec.Fixed.IsFixed
