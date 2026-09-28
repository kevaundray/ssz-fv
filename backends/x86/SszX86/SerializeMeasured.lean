import SszX86.SerializeMeasureOwned
import SszX86.SerializeMemory

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

/-- Registers retained by the real measurement ABI at wrapper PC47. -/
structure MeasureAnchors (s : MachineData) (base : Int64) (t : MachineState) : Prop where
  pc : t.2 = base + 47
  stack : t.1.regs.rsp.toBitVec = wrapperSP s
  result : t.1.regs.rbx = s.regs.rdi
  descriptor : t.1.regs.r12 = s.regs.rsi
  capacity : t.1.regs.r13 = s.regs.r8
  output : t.1.regs.r14 = s.regs.rcx
  value : t.1.regs.r15 = s.regs.rdx
  rbp : t.1.regs.rbp = s.regs.rbp
  vectors : t.1.zmms = s.zmms

theorem measured_anchors {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64} {t : MachineState}
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) : MeasureAnchors s base t := by
  refine ⟨?_, ?_, post.abi.rbx, post.abi.r12, post.abi.r13,
    post.abi.r14, post.abi.r15, post.abi.rbp, post.abi.vectors⟩
  · simpa only [Int64.ofBitVec_toBitVec] using post.abi.returned
  · rw [post.abi.stack, measureState_stack_pointer]
    unfold wrapperSP
    bv_omega

theorem measured_mapping {s : MachineData} {base : Int64} {t : MachineState}
    (mapping : BitVector.Mapping.Extends (measureState s base).dmem t.1.dmem) :
    BitVector.Mapping.Extends s.dmem t.1.dmem := by
  intro p count hm
  exact mapping p count (measureState_extension s base p count hm)

theorem measure_writable_reserved (s : MachineData) (base : Int64)
    (desc : Desc) (value : Value) (address capacity used a : BitVec 64)
    (writes : Measure.Writable (measureState s base)
      (SszNative.Serialize.measure desc value (arenaState address capacity used)) a) :
    Reserved s address capacity used a := by
  apply measure_reserved s base address capacity used a
  rcases writes with result | allocation | ⟨_, cursor⟩ | activation
  · exact Or.inl (Measure.resultWrites_span _ _ _ result)
  · exact Or.inr (Or.inr (Or.inl
      (Measure.allocation_in_free desc value address capacity used a allocation)))
  · exact Or.inr (Or.inl cursor)
  · exact Or.inr (Or.inr (Or.inr activation))

theorem measure_writable_final (s : MachineData) (base : Int64)
    (desc : Desc) (value : Value) (address capacity used a : BitVec 64)
    (writes : Measure.Writable (measureState s base)
      (SszNative.Serialize.measure desc value (arenaState address capacity used)) a) :
    Writable s desc value address capacity used a := by
  have calls : (written s desc value address capacity used).outcome.calls =
      (SszNative.Serialize.measure desc value (arenaState address capacity used)).calls :=
    (serialize_resources desc value s.regs.r8.toNat (arenaState address capacity used)).2
  rcases writes with result | allocation | ⟨allocated, cursor⟩ | activation
  · have inside := Measure.resultWrites_span _ _ _ result
    rw [measureState_plan_pointer] at inside
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (stack_window_span s 112 72 (by decide) (by decide) inside))))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rwa [calls]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, cursor⟩)))
    rwa [calls]
  · rw [measureState_frame_bottom] at activation
    obtain ⟨i, hi, equal⟩ := activation
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega, equal⟩)))

theorem measured_reserved_frame {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used : BitVec 64}
    {t : MachineState}
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) :
    MemoryFrame s.dmem t.1.dmem (Reserved s address capacity used) := by
  intro a outside
  calc
    t.1.dmem.get? a = (measureState s base).dmem.get? a := post.frame a (fun writes =>
      outside (measure_writable_reserved s base desc value address capacity used a writes))
    _ = s.dmem.get? a := measure_frame_stack s base a (fun inside =>
      outside (Or.inr (Or.inr (Or.inr (Or.inr inside)))))

/-- Measurement publication is entirely in the wrapper stack. Its exact retained
allocation trace is the final serialize trace even when a later check fails. -/
theorem measured_frame {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used : BitVec 64}
    {t : MachineState}
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) :
    MemoryFrame s.dmem t.1.dmem (Writable s desc value address capacity used) := by
  intro a outside
  calc
    t.1.dmem.get? a = (measureState s base).dmem.get? a := post.frame a (fun writes =>
      outside (measure_writable_final s base desc value address capacity used a writes))
    _ = s.dmem.get? a := measure_frame_stack s base a (fun inside =>
      outside (Or.inr (Or.inr (Or.inr (Or.inr inside)))))

/-- The five wrapper save slots and original RET slot lie above both the
measurement activation and its 72-byte Plan result. -/
theorem Owned.measure_saved_untouched {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (i : Nat) (hi : i < 48) :
    ¬ Measure.Writable (measureState s base)
      (SszNative.Serialize.measure desc value (arenaState address capacity used))
      (s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 i) := by
  intro writes
  have coordinate : s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 i =
      stackBase s + BitVec.ofNat 64 (384 + i) := by
    unfold stackBase
    bv_omega
  rcases writes with result | allocation | ⟨_, cursor⟩ | activation
  · obtain ⟨j, hj, equal⟩ := Measure.resultWrites_span _ _ _ result
    rw [measureState_plan_pointer] at equal
    unfold planPointer at equal
    bv_omega
  · obtain ⟨j, hj, equal⟩ :=
      Measure.allocation_in_free desc value address capacity used _ allocation
    have arenaBound := owned.arenaBound
    have stackLow := owned.stackLow
    have returnBound := owned.returnBound
    have apart := owned.freeStack
    have equality : address.toNat + used.toNat + j = s.regs.rsp.toNat - 40 + i := by
      simp only [← UInt64.toNat_toBitVec] at stackLow returnBound ⊢
      bv_omega
    unfold Body.Apart at apart
    omega
  · obtain ⟨j, hj, equal⟩ := cursor
    apply owned.headerStack (16 + j) (by omega) (384 + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← coordinate]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := activation
    rw [measureState_frame_bottom] at equal
    unfold stackBase at equal
    bv_omega

theorem Owned.measured_saved {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    {t : MachineState}
    (owned : Owned s base desc value buffer address capacity used ra)
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) : SavedAt t.1.dmem (wrapperSP s) s := by
  apply savedAt_congr (measureState s base).dmem t.1.dmem (wrapperSP s) s
    _ (measureState_saved s base)
  intro i hi
  have coordinate : wrapperSP s + 96#64 + BitVec.ofNat 64 i =
      s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 i := by
    unfold wrapperSP
    bv_omega
  rw [coordinate]
  exact post.frame _ (owned.measure_saved_untouched i (by omega))

theorem Owned.measured_return {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    {t : MachineState}
    (owned : Owned s base desc value buffer address capacity used ra)
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) :
    Mem.loadInt t.1.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have preserved : Mem.loadInt t.1.dmem s.regs.rsp.toBitVec 8 =
      Mem.loadInt (measureState s base).dmem s.regs.rsp.toBitVec 8 := by
    apply Emit.frame_load _ _ _ post.frame
    intro i hi
    have coordinate : s.regs.rsp.toBitVec + BitVec.ofNat 64 i =
        s.regs.rsp.toBitVec - 40 + BitVec.ofNat 64 (40 + i) := by bv_omega
    rw [coordinate]
    exact owned.measure_saved_untouched (40 + i) (by omega)
  exact preserved.trans ((measureState_caller_return s base).trans owned.returnSlot)

theorem Owned.measure_output_untouched {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (i : Nat) (hi : i < s.regs.r8.toNat) :
    ¬ Measure.Writable (measureState s base)
      (SszNative.Serialize.measure desc value (arenaState address capacity used))
      (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) := by
  intro writes
  rcases writes with result | allocation | ⟨_, cursor⟩ | activation
  · have inside := Measure.resultWrites_span _ _ _ result
    rw [measureState_plan_pointer] at inside
    obtain ⟨j, hj, equal⟩ :=
      stack_window_span s 112 72 (by decide) (by decide) inside
    exact owned.outputStack i hi j (by omega) equal
  · obtain ⟨j, hj, equal⟩ :=
      Measure.allocation_in_free desc value address capacity used _ allocation
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
    rw [measureState_frame_bottom] at equal
    exact owned.outputStack i hi j (by omega) equal

theorem Owned.measured_output {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    {t : MachineState}
    (owned : Owned s base desc value buffer address capacity used ra)
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) (i : Nat) (hi : i < s.regs.r8.toNat) :
    t.1.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) := by
  rw [post.frame _ (owned.measure_output_untouched i hi)]
  apply measure_frame_stack s base
  rintro ⟨j, hj, equal⟩
  exact owned.outputStack i hi j (by omega) equal

theorem Owned.measured_borrowed {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    {t : MachineState}
    (owned : Owned s base desc value buffer address capacity used ra)
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) (a : BitVec 64)
    (borrowed : Borrowed s desc value buffer a) :
    t.1.dmem.get? a = s.dmem.get? a :=
  measured_reserved_frame post a
    (owned.readonly a (measure_borrowed_emit s desc value buffer a borrowed))

theorem Owned.measured_emit_table {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    {t : MachineState}
    (owned : Owned s base desc value buffer address capacity used ra)
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) :
    Emit.TableAt t.1.dmem (base + Int64.ofInt emitOffset) := by
  intro i hi
  rw [measured_reserved_frame post _ (owned.emitTableReadonly _ ⟨i, by
    simpa only [Emit.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩)]
  exact owned.emitTable i hi

theorem Owned.measured_resources {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    {t : MachineState}
    (owned : Owned s base desc value buffer address capacity used ra)
    (post : Measure.Post (measureState s base) desc value buffer address capacity used
      (base + 47).toBitVec t) :
    Resources s base desc value buffer address capacity used ra t.1.dmem := by
  exact {
    cursor := post.cursor
    header := post.header
    calls := post.calls
    descriptor := post.descriptor
    valueStored := post.valueStored
    table := owned.measured_emit_table post
    saved := owned.measured_saved post
    returnSlot := owned.measured_return post }

end SszX86.Serialize
