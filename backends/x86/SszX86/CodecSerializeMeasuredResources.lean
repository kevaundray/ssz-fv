import SszX86.CodecSerializeMeasured

namespace SszX86.CodecSerialize
open SszNative UintCodec

section
variable {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64} {t : MachineState}

/-- The full 72-byte return area ends at SP-40, exactly below the five
wrapper saves. The recursive activation ends at SP-144. Neither can touch
any of the five saved words or the original caller's return word. -/
theorem Owned.measure_saved_untouched
    (owned : Owned s base desc value readonly address capacity used ra)
    (i : Nat) (hi : i < 48) :
    ¬ CodecMeasure.Writable (Serialize.measureState s base) desc
      (measured desc value address capacity used).effects
      (s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 i) := by
  intro writes
  have depth := stackBytes_wrapper desc
  have low := owned.stack.lowEnough
  have high := owned.returnBound
  have coordinate : s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 i =
      stackBase s desc + BitVec.ofNat 64 (stackBytes desc - 40 + i) := by
    unfold stackBase
    bv_omega
  rcases writes with result | effects | cursor | activation
  · obtain ⟨j, hj, equal⟩ := result
    rw [Serialize.measureState_plan_pointer] at equal
    unfold Serialize.planPointer at equal
    bv_omega
  · obtain ⟨j, hj, equal⟩ := owned.measure_effects_free _ effects
    have arenaBound := owned.arenaBound
    have apart := owned.freeStack
    have equality : address.toNat + used.toNat + j = s.regs.rsp.toNat - 40 + i := by
      simp only [← UInt64.toNat_toBitVec] at low high ⊢
      bv_omega
    unfold Body.Apart at apart
    omega
  · obtain ⟨j, hj, equal⟩ := cursor
    apply owned.headerStack (16 + j) (by omega) (stackBytes desc - 40 + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← coordinate]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := activation
    rw [measure_bottom] at equal
    simp only [← UInt64.toNat_toBitVec] at low high
    unfold stackBytes at low
    unfold stackBase stackBytes at equal
    bv_omega

theorem Owned.measured_saved
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    Serialize.SavedAt t.1.dmem (Serialize.wrapperSP s) s := by
  apply Serialize.savedAt_congr (Serialize.measureState s base).dmem t.1.dmem
    (Serialize.wrapperSP s) s _ (Serialize.measureState_saved s base)
  intro i hi
  have coordinate : Serialize.wrapperSP s + 96#64 + BitVec.ofNat 64 i =
      s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 i := by
    unfold Serialize.wrapperSP
    bv_omega
  rw [coordinate]
  exact post.frame _ (owned.measure_saved_untouched i (by omega))

theorem Owned.measured_return
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    Mem.loadInt t.1.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have preserved : Mem.loadInt t.1.dmem s.regs.rsp.toBitVec 8 =
      Mem.loadInt (Serialize.measureState s base).dmem s.regs.rsp.toBitVec 8 := by
    apply Emit.frame_load _ _ _ post.frame
    intro i hi
    have coordinate : s.regs.rsp.toBitVec + BitVec.ofNat 64 i =
        s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 (40 + i) := by bv_omega
    rw [coordinate]
    exact owned.measure_saved_untouched (40 + i) (by omega)
  exact preserved.trans ((Serialize.measureState_caller_return s base).trans owned.returnSlot)

theorem Owned.measured_output_untouched
    (owned : Owned s base desc value readonly address capacity used ra)
    (i : Nat) (hi : i < s.regs.r8.toNat) :
    ¬ MeasuredWrites s desc value address capacity used
      (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) := by
  intro writes
  rcases writes with effects | cursor | activation
  · obtain ⟨j, hj, equal⟩ := owned.measure_effects_free _ effects
    have arenaBound := owned.arenaBound
    have outputBound := owned.outputBound
    have apart := owned.freeOutput
    have equality : address.toNat + used.toNat + j = s.regs.rcx.toNat + i := by
      simp only [← UInt64.toNat_toBitVec] at outputBound hi ⊢
      bv_omega
    unfold Body.Apart at apart
    omega
  · obtain ⟨j, hj, equal⟩ := cursor
    apply owned.outputHeader i hi (16 + j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact equal
  · obtain ⟨j, hj, equal⟩ := activation
    exact owned.outputStack i hi j (by omega) equal

/-- Every byte of the original capacity is preserved, even for failed
measurement and without excluding empty buffers or readonly aliases. -/
theorem Owned.measured_output
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t)
    (i : Nat) (hi : i < s.regs.r8.toNat) :
    t.1.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) :=
  measured_frame post _ (owned.measured_output_untouched i hi)

theorem Owned.measured_measure_table
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    CodecMeasure.TableAt t.1.dmem (base + Int64.ofInt measureOffset) := by
  intro i hi
  rw [owned.measured_borrowed post _ (owned.measureTableReadonly _ ⟨i, by
    simpa only [CodecMeasure.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩)]
  exact owned.measureTable i hi

theorem Owned.measured_emit_table
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    CodecEmit.TableAt t.1.dmem (base + Int64.ofInt emitOffset) := by
  intro i hi
  rw [owned.measured_borrowed post _ (owned.emitTableReadonly _ ⟨i, by
    simpa only [CodecEmit.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩)]
  exact owned.emitTable i hi

theorem Owned.measured_emitParts_table
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    CodecEmit.Table1At t.1.dmem (base + Int64.ofInt emitOffset) := by
  intro i hi
  rw [owned.measured_borrowed post _ (owned.emitPartsTableReadonly _ ⟨i, by
    simpa only [CodecEmit.table1Bytes, List.length_cons, List.length_nil] using hi, rfl⟩)]
  exact owned.emitPartsTable i hi

theorem Owned.measured_classifier_table
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    CodecIsFixed.TableAt t.1.dmem
      ((base + Int64.ofInt measureOffset) + Int64.ofInt CodecMeasure.isFixedOffset) := by
  intro i hi
  rw [owned.measured_borrowed post _ (owned.classifierTableReadonly _ ⟨i, by
    simpa only [CodecIsFixed.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩)]
  exact owned.classifierTable i hi

end
end SszX86.CodecSerialize
