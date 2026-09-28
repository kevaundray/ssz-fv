import SszX86.SerializeCore
import SszX86.SerializeStack

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

/-- After measurement, only output/result and the lower 384 stack bytes can
change. Saved words and the caller return slot are above this interval. -/
def LaterWrites (s : MachineData) (a : BitVec 64) : Prop :=
  InSpan a s.regs.rdi.toBitVec 80 ∨
  InSpan a s.regs.rcx.toBitVec s.regs.r8.toNat ∨ InSpan a (stackBase s) 384

theorem later_reserved (s : MachineData) (address capacity used a : BitVec 64)
    (writes : LaterWrites s a) : Reserved s address capacity used a := by
  rcases writes with result | output | ⟨i, hi, equal⟩
  · exact Or.inl result
  · exact Or.inr (Or.inl output)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega, equal⟩)))

theorem desc_live_span (p : BitVec 64) (desc : Desc) (a : BitVec 64)
    (live : Measure.DescLive p desc a) : InSpan a p (Emit.descBytes desc) := by
  rcases live with ⟨i, hi, equal⟩ | payload
  · refine ⟨i, ?_, equal⟩
    cases desc <;> simp only [Emit.descBytes] <;> omega
  · cases desc with
    | bool => cases payload
    | uint operand | byteVector operand | byteList operand | bitVector operand | bitList operand =>
      exact Emit.span_shift p 8 16 24 (by decide) payload
    | progressiveBitList limit =>
      cases limit with
      | none => exact Emit.span_shift p 8 4 32 (by decide) payload
      | some operand =>
        rcases payload with tag | number
        · exact Emit.span_shift p 8 4 32 (by decide) tag
        · exact Emit.span_shift p 16 16 32 (by decide) number

theorem value_live_span (p : BitVec 64) (value : Value) (a : BitVec 64)
    (live : Measure.ValueLive p value a) : InSpan a p (Emit.valueBytes value) := by
  rcases live with ⟨i, hi, equal⟩ | payload
  · refine ⟨i, ?_, equal⟩
    cases value <;> simp only [Emit.valueBytes] <;> omega
  · cases value with
    | bool boolean => exact Emit.span_shift p 1 1 24 (by decide) payload
    | uint number | bytes number => exact Emit.span_shift p 8 16 24 (by decide) payload
    | bits bits => exact Emit.span_shift p 16 32 48 (by decide) payload
    | seq values | union selector values => cases payload

theorem free_disjoint (address capacity used p : BitVec 64) (n : Nat)
    (bound : address.toNat + capacity.toNat ≤ 2 ^ 64)
    (pBound : p.toNat + n ≤ 2 ^ 64)
    (apart : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
      p.toNat n) : Large.Disjoint (address + used) p (capacity.toNat - used.toNat) n := by
  by_cases nonempty : used.toNat < capacity.toNat
  · have start : (address + used).toNat = address.toNat + used.toNat := by bv_omega
    apply Body.apart_bytes
    · rw [start]; omega
    · exact pBound
    · simpa only [start] using apart
  · intro i hi
    omega

theorem Owned.later_free {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (a : BitVec 64) (free : InSpan a (address + used) (capacity.toNat - used.toNat)) :
    ¬ LaterWrites s a := by
  obtain ⟨i, hi, equal⟩ := free
  intro writes
  rcases writes with ⟨j, hj, result⟩ | ⟨j, hj, output⟩ | ⟨j, hj, scratch⟩
  · exact free_disjoint address capacity used s.regs.rdi.toBitVec 80 owned.arenaBound
      owned.resultBound owned.freeResult i hi j hj (equal.symm.trans result)
  · exact free_disjoint address capacity used s.regs.rcx.toBitVec s.regs.r8.toNat
      owned.arenaBound owned.outputBound owned.freeOutput i hi j hj (equal.symm.trans output)
  · have low := owned.stackLow
    have upper := owned.returnBound
    have sp : (stackBase s).toNat = s.regs.rsp.toNat - 424 := by
      simp only [stackBase, ← UInt64.toNat_toBitVec] at low ⊢
      bv_omega
    have bound : (stackBase s).toNat + 432 ≤ 2 ^ 64 := by rw [sp]; omega
    have apart : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
        (stackBase s).toNat 432 := by simpa only [sp] using owned.freeStack
    exact free_disjoint address capacity used (stackBase s) 432 owned.arenaBound
      bound apart i hi j (by omega) (equal.symm.trans scratch)

theorem Owned.later_header {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (a : BitVec 64) (header : InSpan a s.regs.r9.toBitVec 24) : ¬ LaterWrites s a := by
  obtain ⟨i, hi, equal⟩ := header
  intro writes
  rcases writes with ⟨j, hj, result⟩ | ⟨j, hj, output⟩ | ⟨j, hj, scratch⟩
  · exact owned.resultHeader j hj i hi (result.symm.trans equal)
  · exact owned.outputHeader j hj i hi (output.symm.trans equal)
  · exact owned.headerStack i hi j (by omega) (equal.symm.trans scratch)

theorem Owned.later_saved {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (i : Nat) (hi : i < 48) :
    ¬ LaterWrites s (stackBase s + BitVec.ofNat 64 (384 + i)) := by
  intro writes
  rcases writes with ⟨j, hj, result⟩ | ⟨j, hj, output⟩ | ⟨j, hj, scratch⟩
  · exact owned.resultStack j hj (384 + i) (by omega) result.symm
  · exact owned.outputStack j hj (384 + i) (by omega) output.symm
  · bv_omega

/-- Resource observations established by the completed measurement, retained
through wrapper publication and successful emit without rolling anything back. -/
structure Resources (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (m : DataMem) : Prop where
  cursor : widthLoad m (s.regs.r9.toNat + 16) 8 =
    some (SszNative.Serialize.measure desc value (arenaState address capacity used)).used
  header : widthLoad m s.regs.r9.toNat 8 = some address.toNat ∧
    widthLoad m (s.regs.r9.toNat + 8) 8 = some capacity.toNat
  calls : Measure.CallsAt (widthLoad m)
    (SszNative.Serialize.measure desc value (arenaState address capacity used)).calls
  descriptor : Emit.DescAt m s.regs.rsi.toBitVec desc
  valueStored : Emit.ValueAt m s.regs.rdx.toBitVec buffer value
  table : Emit.TableAt m (base + Int64.ofInt emitOffset)
  saved : SavedAt m (wrapperSP s) s
  returnSlot : Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))

theorem Resources.transport {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {before after : DataMem}
    (owned : Owned s base desc value buffer address capacity used ra)
    (resources : Resources s base desc value buffer address capacity used ra before)
    (frame : MemoryFrame before after (LaterWrites s)) :
    Resources s base desc value buffer address capacity used ra after := by
  have header (off n : Nat) (inside : off + n ≤ 24) :
      widthLoad after (s.regs.r9.toNat + off) n =
        widthLoad before (s.regs.r9.toNat + off) n := by
    simp only [← UInt64.toNat_toBitVec]
    unfold widthLoad
    rw [width_address]
    congr 1
    exact Measure.frame_load_window before after (LaterWrites s) frame
      s.regs.r9.toBitVec off n 24 inside (owned.later_header)
  have borrowed (a : BitVec 64) (input : Emit.Borrowed s desc value buffer a) :
      ¬ LaterWrites s a := fun writes => owned.readonly a input
        (later_reserved s address capacity used a writes)
  refine {
    cursor := (header 16 8 (by decide)).trans resources.cursor
    header := ⟨?_, (header 8 8 (by decide)).trans resources.header.2⟩
    calls := ?_
    descriptor := ?_
    valueStored := ?_
    table := ?_
    saved := ?_
    returnSlot := ?_ }
  · simpa only [Nat.add_zero] using (header 0 8 (by decide)).trans resources.header.1
  · intro call member reservation allocated i
    have same := Measure.frame_load_window before after (LaterWrites s) frame
      (BitVec.ofNat 64 reservation.pointer) (8 * i.val) 8 (8 * call.written.length)
      (by have inside := i.isLt; omega) (by
        intro a inside
        exact owned.later_free a (Measure.allocation_in_free desc value address capacity used a
          ⟨call, member, reservation, allocated, inside⟩))
    unfold widthLoad
    rw [BitVec.ofNat_add, same]
    simpa only [widthLoad, BitVec.ofNat_add] using resources.calls call member reservation allocated i
  · apply Measure.descriptor_frame before after (LaterWrites s) frame
      s.regs.rsi.toBitVec desc _ resources.descriptor
    intro a input
    rcases input with live | limbs
    · exact borrowed a (Or.inl (desc_live_span _ _ _ live))
    · exact borrowed a (Or.inr (Or.inr (Or.inl limbs)))
  · apply Measure.value_frame before after (LaterWrites s) frame
      s.regs.rdx.toBitVec buffer value _ resources.valueStored
    intro a input
    rcases input with live | backing
    · exact borrowed a (Or.inr (Or.inl (value_live_span _ _ _ live)))
    · exact borrowed a (Or.inr (Or.inr (Or.inr backing)))
  · intro i hi
    rw [frame _ (fun writes => owned.emitTableReadonly _ ⟨i, hi, rfl⟩
      (later_reserved s address capacity used _ writes))]
    exact resources.table i hi
  · apply savedAt_congr before after (wrapperSP s) s _ resources.saved
    intro i hi
    apply frame
    have same : wrapperSP s + 96 + BitVec.ofNat 64 i =
        stackBase s + BitVec.ofNat 64 (384 + i) := by
      simp only [wrapperSP, stackBase]
      bv_omega
    have untouched := owned.later_saved i (by omega)
    rw [← same] at untouched
    with_unfolding_all exact untouched
  · rw [Emit.frame_load before after (LaterWrites s) frame s.regs.rsp.toBitVec 8]
    · exact resources.returnSlot
    · intro i hi
      have same : s.regs.rsp.toBitVec + BitVec.ofNat 64 i =
          stackBase s + BitVec.ofNat 64 (384 + (40 + i)) := by
        simp only [stackBase]
        bv_omega
      rw [same]
      exact owned.later_saved (40 + i) (by omega)

end SszX86.Serialize
