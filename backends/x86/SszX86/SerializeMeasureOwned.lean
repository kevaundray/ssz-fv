import SszX86.SerializeCore
import SszX86.SerializeEdges
import SszX86.SerializeMemory

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

@[simp] theorem measureState_descriptor_pointer (s : MachineData) (base : Int64) :
    (measureState s base).regs.rsi = s.regs.rsi := rfl

@[simp] theorem measureState_value_pointer (s : MachineData) (base : Int64) :
    (measureState s base).regs.rdx = s.regs.rdx := rfl

@[simp] theorem measureState_arena_pointer (s : MachineData) (base : Int64) :
    (measureState s base).regs.rcx = s.regs.r9 := rfl

@[simp] theorem measureState_plan_pointer (s : MachineData) (base : Int64) :
    (measureState s base).regs.rdi.toBitVec = planPointer s := by
  simp only [measureState, prologueState, planPointer, UInt64.toBitVec_ofBitVec]

@[simp] theorem measureState_stack_pointer (s : MachineData) (base : Int64) :
    (measureState s base).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 144 := by
  simp only [measureState, UInt64.toBitVec_ofBitVec]

@[simp] theorem measureState_result_anchor (s : MachineData) (base : Int64) :
    (measureState s base).regs.rbx = s.regs.rdi := rfl

@[simp] theorem measureState_descriptor_anchor (s : MachineData) (base : Int64) :
    (measureState s base).regs.r12 = s.regs.rsi := rfl

@[simp] theorem measureState_capacity_anchor (s : MachineData) (base : Int64) :
    (measureState s base).regs.r13 = s.regs.r8 := rfl

@[simp] theorem measureState_output_anchor (s : MachineData) (base : Int64) :
    (measureState s base).regs.r14 = s.regs.rcx := rfl

@[simp] theorem measureState_value_anchor (s : MachineData) (base : Int64) :
    (measureState s base).regs.r15 = s.regs.rdx := rfl

@[simp] theorem measureState_frame_bottom (s : MachineData) (base : Int64) :
    (measureState s base).regs.rsp.toBitVec - 280 = stackBase s := by
  rw [measureState_stack_pointer]
  unfold stackBase
  bv_omega

theorem stack_window_span (s : MachineData) (distance count : Nat)
    (fits : count ≤ distance) (within : distance ≤ 424) {a : BitVec 64}
    (inside : InSpan a (s.regs.rsp.toBitVec - BitVec.ofNat 64 distance) count) :
    InSpan a (stackBase s) 424 := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨424 - distance + i, by omega, ?_⟩
  unfold stackBase
  bv_omega

theorem Owned.stack_subrange_mapped {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (distance count : Nat) (fits : count ≤ distance) (within : distance ≤ 424) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - BitVec.ofNat 64 distance) count := by
  have hm := Delimited.Reservation.mapped_subrange s.dmem (stackBase s)
    424 (424 - distance) count owned.stackMapped (by omega)
  have pointer : stackBase s + BitVec.ofNat 64 (424 - distance) =
      s.regs.rsp.toBitVec - BitVec.ofNat 64 distance := by
    unfold stackBase
    bv_omega
  rwa [pointer] at hm

theorem Owned.entry_stack_mapped {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 144) 144 :=
  owned.stack_subrange_mapped 144 144 (by decide) (by decide)

theorem measure_frame_stack (s : MachineData) (base : Int64) :
    MemoryFrame s.dmem (measureState s base).dmem
      (fun a => InSpan a (stackBase s) 424) := by
  intro a outside
  apply measureState_frame s base a
  rintro (saved | call)
  · exact outside (stack_window_span s 40 40 (by decide) (by decide) saved)
  · exact outside (stack_window_span s 144 8 (by decide) (by decide) call)

theorem measure_borrowed_emit (s : MachineData) (desc : Desc) (value : Value)
    (buffer a : BitVec 64) (borrowed : Measure.Borrowed s desc value buffer a) :
    Emit.Borrowed s desc value buffer a := by
  rcases borrowed with descriptor | valueLive | descriptorLimbs | valueBytes
  · exact Or.inl (desc_live_span _ _ _ descriptor)
  · exact Or.inr (Or.inl (value_live_span _ _ _ valueLive))
  · exact Or.inr (Or.inr (Or.inl descriptorLimbs))
  · exact Or.inr (Or.inr (Or.inr valueBytes))

theorem Owned.measure_descriptor {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Emit.DescAt (measureState s base).dmem s.regs.rsi.toBitVec desc := by
  apply Measure.descriptor_frame s.dmem _ _ (measure_frame_stack s base)
    _ desc _ owned.descriptor
  intro a borrowed inside
  apply owned.readonly a _ (Or.inr (Or.inr (Or.inr (Or.inr inside))))
  rcases borrowed with live | limbs
  · exact Or.inl (desc_live_span _ _ _ live)
  · exact Or.inr (Or.inr (Or.inl limbs))

theorem Owned.measure_value {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Emit.ValueAt (measureState s base).dmem s.regs.rdx.toBitVec buffer value := by
  apply Measure.value_frame s.dmem _ _ (measure_frame_stack s base)
    _ buffer value _ owned.valueStored
  intro a borrowed inside
  apply owned.readonly a _ (Or.inr (Or.inr (Or.inr (Or.inr inside))))
  rcases borrowed with live | bytes
  · exact Or.inr (Or.inl (value_live_span _ _ _ live))
  · exact Or.inr (Or.inr (Or.inr bytes))

theorem Owned.measure_arena {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Measure.ArenaAt (measureState s base).dmem s.regs.r9.toBitVec address capacity used := by
  have fields (off : Nat) (bound : off + 8 ≤ 24) :
      widthLoad (measureState s base).dmem (s.regs.r9.toNat + off) 8 =
        widthLoad s.dmem (s.regs.r9.toNat + off) 8 := by
    unfold widthLoad
    rw [← UInt64.toNat_toBitVec, width_address]
    congr 1
    apply Emit.frame_load s.dmem _ _ (measure_frame_stack s base)
    intro i hi inside
    obtain ⟨j, hj, equal⟩ := inside
    apply owned.headerStack (off + i) (by omega) j (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact equal
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, UInt64.toNat_toBitVec] using
      (fields 0 (by decide)).trans owned.arena.1
  · exact (fields 8 (by decide)).trans owned.arena.2.1
  · exact (fields 16 (by decide)).trans owned.arena.2.2

theorem Owned.measure_table {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Measure.TableAt (measureState s base).dmem (base + Int64.ofInt measureOffset) := by
  intro i hi
  rw [measure_frame_stack s base _ (by
    intro inside
    apply owned.measureTableReadonly _ ⟨i, by
      simpa only [Measure.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr inside))))]
  exact owned.measureTable i hi

theorem Owned.measure_emit_table {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Emit.TableAt (measureState s base).dmem (base + Int64.ofInt emitOffset) := by
  intro i hi
  rw [measure_frame_stack s base _ (by
    intro inside
    apply owned.emitTableReadonly _ ⟨i, by
      simpa only [Emit.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr inside))))]
  exact owned.emitTable i hi

theorem Owned.measure_stack_nat {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    (measureState s base).regs.rsp.toNat = s.regs.rsp.toNat - 144 := by
  have low := owned.stackLow
  simp only [← UInt64.toNat_toBitVec] at low ⊢
  rw [measureState_stack_pointer]
  bv_omega

theorem Owned.plan_pointer_nat {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    (planPointer s).toNat = s.regs.rsp.toNat - 112 := by
  have low := owned.stackLow
  simp only [← UInt64.toNat_toBitVec] at low ⊢
  unfold planPointer
  bv_omega

theorem measure_reserved (s : MachineData) (base : Int64)
    (address capacity used a : BitVec 64)
    (writes : InSpan a (measureState s base).regs.rdi.toBitVec 72 ∨
      InSpan a ((measureState s base).regs.rcx.toBitVec + 16) 8 ∨
      InSpan a (address + used) (capacity.toNat - used.toNat) ∨
      InSpan a ((measureState s base).regs.rsp.toBitVec - 280) 280) :
    Reserved s address capacity used a := by
  simp only [measureState_plan_pointer, measureState_arena_pointer,
    measureState_frame_bottom] at writes
  rcases writes with plan | header | arena | activation
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (stack_window_span s 112 72 (by decide) (by decide) plan))))
  · exact Or.inr (Or.inr (Or.inl header))
  · exact Or.inr (Or.inr (Or.inr (Or.inl arena)))
  · obtain ⟨i, hi, equal⟩ := activation
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega, equal⟩)))

/-- Every callee obligation follows from original ownership and the exact five
PUSH stores plus CALL42. The Plan remains uninitialized at this callsite. -/
theorem Owned.measure_owned {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) :
    Measure.Owned (measureState s base) (base + Int64.ofInt measureOffset)
      desc value buffer address capacity used (base + 47).toBitVec true := by
  have low := owned.stackLow
  have high := owned.returnBound
  have stackNat := owned.measure_stack_nat
  have planNat : (measureState s base).regs.rdi.toNat = s.regs.rsp.toNat - 112 := by
    rw [← UInt64.toNat_toBitVec, measureState_plan_pointer]
    exact owned.plan_pointer_nat
  have bottomNat : (measureState s base).regs.rsp.toNat - 280 =
      s.regs.rsp.toNat - 424 := by omega
  have planMapped : Large.Mapped s.dmem (planPointer s) 72 :=
    owned.stack_subrange_mapped 112 72 (by decide) (by decide)
  have localMapped : Large.Mapped s.dmem (stackBase s) 280 := by
    intro i hi
    exact owned.stackMapped i (by omega)
  refine {
    physical := owned.physical
    descriptor := owned.measure_descriptor
    descriptorMapped := measureState_extension s base _ _ owned.descriptorMapped
    valueStored := owned.measure_value
    retainFlag := by
      change (1 : UInt64).toBitVec.setWidth 8 = BitVec.ofNat 8 1
      decide
    arena := owned.measure_arena
    descriptorBound := owned.descriptorBound
    valueBound := owned.valueBound
    resultBound := by omega
    headerBound := owned.headerBound
    stackLow := by omega
    returnBound := by omega
    arenaBound := owned.arenaBound
    arenaNonzero := owned.arenaNonzero
    resultMapped := ?_
    stackMapped := ?_
    freeMapped := measureState_extension s base _ _ owned.freeMapped
    returnSlot := measureState_return_load s base
    resultHeader := ?_
    resultStack := ?_
    headerStack := ?_
    freeResult := ?_
    freeHeader := owned.freeHeader
    freeStack := ?_
    readonly := ?_
    table := owned.measure_table
    tableReadonly := ?_ }
  · rw [measureState_plan_pointer]
    exact measureState_extension s base _ _ planMapped
  · rw [measureState_frame_bottom]
    exact measureState_extension s base _ _ localMapped
  · simp only [measureState_plan_pointer, measureState_arena_pointer]
    intro i hi j hj equal
    apply owned.headerStack j hj (312 + i) (by omega)
    have pointer : planPointer s + BitVec.ofNat 64 i =
        stackBase s + BitVec.ofNat 64 (312 + i) := by
      unfold planPointer stackBase
      bv_omega
    exact equal.symm.trans pointer
  · simp only [measureState_plan_pointer, measureState_frame_bottom]
    intro i hi j hj
    unfold planPointer stackBase
    bv_omega
  · simp only [measureState_arena_pointer, measureState_frame_bottom]
    intro i hi j hj
    exact owned.headerStack i hi j (by omega)
  · rw [planNat]
    have apart := owned.freeStack
    unfold Body.Apart at apart ⊢
    omega
  · rw [bottomNat]
    have apart := owned.freeStack
    unfold Body.Apart at apart ⊢
    omega
  · intro a borrowed writes
    have original : Measure.Borrowed s desc value buffer a := by
      simpa only [Measure.Borrowed, measureState_descriptor_pointer,
        measureState_value_pointer] using borrowed
    exact owned.readonly a (measure_borrowed_emit s desc value buffer a original)
      (measure_reserved s base address capacity used a writes)
  · intro a table writes
    exact owned.measureTableReadonly a table
      (measure_reserved s base address capacity used a writes)

end SszX86.Serialize
