import SszX86.MeasureFrame
import SszX86.MeasureOutputMemory

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

theorem BodyOwned.publication_descriptor {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (m : DataMem) (outcome : Outcome NatOperand)
    (frame : MemoryFrame s.dmem m (ResultWrites s.regs.rbx.toBitVec outcome)) :
    DescAt m s.regs.rsi.toBitVec desc := by
  apply descriptor_frame s.dmem m _ frame _ desc _ owned.descriptor
  intro a borrowed writable
  have inside := resultWrites_span _ _ _ writable
  apply owned.readonly a _ (Or.inl inside)
  rcases borrowed with live | limbs
  · exact Or.inl live
  · exact Or.inr (Or.inr (Or.inl limbs))

theorem BodyOwned.publication_value {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (m : DataMem) (outcome : Outcome NatOperand)
    (frame : MemoryFrame s.dmem m (ResultWrites s.regs.rbx.toBitVec outcome)) :
    ValueAt m s.regs.r14.toBitVec buffer value := by
  apply value_frame s.dmem m _ frame _ buffer value _ owned.valueStored
  intro a borrowed writable
  have inside := resultWrites_span _ _ _ writable
  apply owned.readonly a _ (Or.inl inside)
  rcases borrowed with live | bytes
  · exact Or.inr (Or.inl live)
  · exact Or.inr (Or.inr (Or.inr bytes))

theorem BodyOwned.publication_operand {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (m : DataMem) (outcome : Outcome NatOperand) (operand : NatOperand)
    (frame : MemoryFrame s.dmem m (ResultWrites s.regs.rbx.toBitVec outcome))
    (borrowed : ∀ a, Emit.NatBorrowed operand a → BodyBorrowed s desc value buffer a)
    (stored : operand.At (widthLoad s.dmem)) : operand.At (widthLoad m) := by
  apply operand_frame s.dmem m _ frame operand _ stored
  intro a inside writable
  exact owned.readonly a (borrowed a inside) (Or.inl (resultWrites_span _ _ _ writable))

theorem BodyOwned.publication_header {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (m : DataMem) (outcome : Outcome NatOperand)
    (frame : MemoryFrame s.dmem m (ResultWrites s.regs.rbx.toBitVec outcome)) :
    ArenaAt m s.regs.rcx.toBitVec address capacity used := by
  have fields (off : Nat) (bound : off + 8 ≤ 24) :
      widthLoad m (s.regs.rcx.toNat + off) 8 =
        widthLoad s.dmem (s.regs.rcx.toNat + off) 8 := by
    unfold widthLoad
    rw [← UInt64.toNat_toBitVec, width_address]
    congr 1
    apply frame_load s.dmem m _ frame
    intro i hi writes
    obtain ⟨j, hj, equal⟩ := resultWrites_span _ _ _ writes
    apply owned.resultHeader j hj (off + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact equal.symm
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, UInt64.toNat_toBitVec] using
      (fields 0 (by decide)).trans owned.arena.1
  · exact (fields 8 (by decide)).trans owned.arena.2.1
  · exact (fields 16 (by decide)).trans owned.arena.2.2

/-- A publication-only execution has no hidden allocation: input ownership and
all three arena words follow from the original disjointness, not exit premises. -/
theorem noalloc_body_post (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) (result : Except Error NatOperand)
    (owned : BodyOwned s desc value buffer address capacity used)
    (model : measure desc value (arenaState address capacity used) = unchanged used.toNat result)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms)
    (observed : ResultAt (widthLoad t.dmem) s.regs.rbx.toNat result)
    (frame : MemoryFrame s.dmem t.dmem
      (ResultWrites s.regs.rbx.toBitVec (unchanged used.toNat result))) :
    BodyPost s desc value buffer address capacity used t := by
  have header := owned.publication_header t.dmem (unchanged used.toNat result) frame
  refine ⟨stack, ?_, ?_, ⟨header.1, header.2.1⟩, ?_,
    owned.publication_descriptor t.dmem (unchanged used.toNat result) frame,
    owned.publication_value t.dmem (unchanged used.toNat result) frame, ?_, vectors⟩
  · simpa only [model, unchanged] using observed
  · simpa only [model, unchanged, UInt64.toNat_toBitVec] using header.2.2
  · simp only [model, unchanged, CallsAt, List.not_mem_nil, false_implies, implies_true]
  · intro a outside
    apply frame a
    intro written
    exact outside (Or.inl (by simpa only [model] using written))

end SszX86.Measure
