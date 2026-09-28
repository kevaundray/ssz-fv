import SszX86.SerializeMemory
import SszX86.SerializeEdges
import SszX86.SerializeHost

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

structure AtWrapper (s t : MachineData) : Prop where
  stack : t.regs.rsp.toBitVec = wrapperSP s
  rbx : t.regs.rbx = s.regs.rdi
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.rsi
  r13 : t.regs.r13 = s.regs.r8
  r14 : t.regs.r14 = s.regs.rcx
  r15 : t.regs.r15 = s.regs.rdx
  vectors : t.zmms = s.zmms

theorem AtWrapper.host {s t u : MachineData} (anchors : AtWrapper s t)
    (frame : HostFrame t u) : AtWrapper s u := by
  have registers (r : Reg64) (hc : r ≠ .rcx) (hd : r ≠ .rdx) (h9 : r ≠ .r9) :=
    frame.registers r hc hd h9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.vectors.trans anchors.vectors⟩
  · exact (registers .rsp (by decide) (by decide) (by decide)).trans anchors.stack
  all_goals apply UInt64.toBitVec_inj.1
  · exact (registers .rbx (by decide) (by decide) (by decide)).trans
      (congrArg UInt64.toBitVec anchors.rbx)
  · exact (registers .rbp (by decide) (by decide) (by decide)).trans
      (congrArg UInt64.toBitVec anchors.rbp)
  · exact (registers .r12 (by decide) (by decide) (by decide)).trans
      (congrArg UInt64.toBitVec anchors.r12)
  · exact (registers .r13 (by decide) (by decide) (by decide)).trans
      (congrArg UInt64.toBitVec anchors.r13)
  · exact (registers .r14 (by decide) (by decide) (by decide)).trans
      (congrArg UInt64.toBitVec anchors.r14)
  · exact (registers .r15 (by decide) (by decide) (by decide)).trans
      (congrArg UInt64.toBitVec anchors.r15)

theorem writes_size_le (s : MachineData) (desc : Desc) (value : Value)
    (address capacity used : BitVec 64) (physical : value.Physical) :
    (written s desc value address capacity used).writes.size ≤ s.regs.r8.toNat := by
  cases outcome : (written s desc value address capacity used).outcome.result with
  | ok n =>
    have success := serialize_success desc value s.regs.r8.toNat
      (arenaState address capacity used) physical n outcome
    rw [written, success.2.1]
    exact success.2.2
  | error reason =>
    have failure := serialize_failure_writes desc value s.regs.r8.toNat
      (arenaState address capacity used) reason outcome
    rw [written, failure]
    exact Nat.zero_le _

theorem result_writes_span (out : BitVec 64) (measured : Outcome NatOperand)
    (result : Except Error Nat) (a : BitVec 64) (writes : ResultWrites out measured result a) :
    InSpan a out 80 := by
  cases first : measured.result with
  | error reason =>
    simp only [ResultWrites, first] at writes
    obtain ⟨i, hi, equal⟩ := writes
    exact ⟨i, by omega, equal⟩
  | ok operand =>
    cases result with
    | error reason =>
      simp only [ResultWrites, first] at writes
      obtain ⟨i, hi, equal⟩ := writes
      exact ⟨i, by omega, equal⟩
    | ok n =>
      simp only [ResultWrites, first] at writes
      rcases writes with ⟨i, hi, equal⟩ | status
      · exact ⟨i, by omega, equal⟩
      · exact Emit.span_shift out 64 4 80 (by decide) status

theorem writable_reserved (s : MachineData) (desc : Desc) (value : Value)
    (address capacity used a : BitVec 64) (physical : value.Physical)
    (writes : Writable s desc value address capacity used a) :
    Reserved s address capacity used a := by
  rcases writes with result | output | allocation | ⟨allocated, cursor⟩ | scratch
  · exact Or.inl (result_writes_span _ _ _ _ result)
  · obtain ⟨i, hi, equal⟩ := output
    have bound := writes_size_le s desc value address capacity used physical
    exact Or.inr (Or.inl ⟨i, by omega, equal⟩)
  · have calls := (serialize_resources desc value s.regs.r8.toNat
      (arenaState address capacity used)).2
    change Measure.AllocationWrites
      (SszNative.Serialize.serialize desc value s.regs.r8.toNat
        (arenaState address capacity used)).outcome.calls a at allocation
    rw [calls] at allocation
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (Measure.allocation_in_free desc value address capacity used a allocation))))
  · exact Or.inr (Or.inr (Or.inl cursor))
  · exact Or.inr (Or.inr (Or.inr (Or.inr scratch)))

theorem borrowed_emit (s : MachineData) (desc : Desc) (value : Value)
    (buffer a : BitVec 64) (borrowed : Borrowed s desc value buffer a) :
    Emit.Borrowed s desc value buffer a := by
  rcases borrowed with descriptor | stored | limbs | backing
  · exact Or.inl (desc_live_span _ _ _ descriptor)
  · exact Or.inr (Or.inl (value_live_span _ _ _ stored))
  · exact Or.inr (Or.inr (Or.inl limbs))
  · exact Or.inr (Or.inr (Or.inr backing))

structure FinishMemory (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (m : DataMem) : Prop where
  resources : Resources s base desc value buffer address capacity used ra m
  observed : ResultAt (widthLoad m) s.regs.rdi.toNat
    (written s desc value address capacity used).outcome.result
  outputFrame : ∀ i < s.regs.r8.toNat,
    m.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) =
      applyWrites (fun j => s.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 j))
        (written s desc value address capacity used).writes i
  frame : MemoryFrame s.dmem m (Writable s desc value address capacity used)

/-- The common epilogue is actually executed after either publication or emit. -/
theorem finish_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra)
    (anchors : AtWrapper s t)
    (memory : FinishMemory s base desc value buffer address capacity used ra t.dmem) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (t, base + 410) := by
  apply epilogue_cps e base hc t s ra
  · simpa only [anchors.stack] using memory.resources.saved
  · have pointer : t.regs.rsp.toBitVec + 136 = s.regs.rsp.toBitVec := by
      rw [anchors.stack]
      simp only [wrapperSP]
      bv_omega
    simpa only [pointer] using memory.resources.returnSlot
  · apply Eventually.done
    have resources := serialize_resources desc value s.regs.r8.toNat
      (arenaState address capacity used)
    refine {
      abi := ?_
      observed := memory.observed
      cursor := ?_
      header := memory.resources.header
      calls := ?_
      descriptor := memory.resources.descriptor
      valueStored := memory.resources.valueStored
      borrowedFrame := ?_
      outputFrame := memory.outputFrame
      frame := memory.frame }
    · refine ⟨rfl, ?_, rfl, anchors.rbp, rfl, rfl, rfl, rfl, anchors.vectors⟩
      simp only [returnedState, UInt64.toBitVec_ofBitVec, anchors.stack, wrapperSP]
      bv_omega
    · simpa only [returnedState, written, resources.1] using memory.resources.cursor
    · simpa only [returnedState, written, resources.2] using memory.resources.calls
    · intro a borrowed
      exact memory.frame a (fun writes => owned.readonly a
        (borrowed_emit s desc value buffer a borrowed)
        (writable_reserved s desc value address capacity used a owned.physical writes))

end SszX86.Serialize
