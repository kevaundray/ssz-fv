import SszX86.CodecMeasureFixedOutputSaved
import SszX86.CodecMeasureFixedMemory
import SszX86.CodecMeasureFixedArithmeticTraceGeometry
import SszX86.MeasureFrame

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec

/-- Writes already performed by the completed recursive/arithmetic prefix. -/
def PrefixWrites (s : MachineData) (bytes : Nat)
    (outcome : Serialize.Outcome (Option NatOperand)) (a : BitVec 64) : Prop :=
  Codec.StackWrites s.regs.rsp.toBitVec bytes a ∨ AllocationWrites outcome.calls a ∨
    (Allocated outcome.calls ∧ Codec.InSpan a (s.regs.rdx.toBitVec + 16) 8)

/-- Evidence at an actual publication cut, not evidence about future execution. -/
structure Pending (original : MachineData) (desc : SszNative.Codec.Desc)
    (address capacity used ra : BitVec 64) (bytes : Nat) (body : MachineData) : Prop where
  sp : body.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136#64
  output : body.regs.rbx.toBitVec = original.regs.rdi.toBitVec
  simd : body.zmms = original.zmms
  saved : SavedAt body.dmem body.regs.rsp.toBitVec (originalSaved original ra)
  «mapped» : Large.Mapped body.dmem body.regs.rbx.toBitVec 72
  cursor : widthLoad body.dmem (original.regs.rdx.toNat + 16) 8 =
    some (FixedSize.measureFixed desc (arenaState address capacity used)).used
  calls : CallsAt (widthLoad body.dmem)
    (FixedSize.measureFixed desc (arenaState address capacity used)).calls
  frame : Codec.MemoryFrame original.dmem body.dmem
    (PrefixWrites original bytes (FixedSize.measureFixed desc (arenaState address capacity used)))

theorem result_writes_span (out : BitVec 64)
    (result : Except Serialize.Error (Option NatOperand)) (a : BitVec 64)
    (written : ResultWrites out result a) : Codec.InSpan a out 72 := by
  cases result with
  | error error => exact written
  | ok width =>
    cases width <;> rcases written with ⟨i, hi, equal⟩ | inside
    · exact ⟨i, by omega, equal⟩
    · exact Measure.span_shift out 64 4 72 (by decide) inside
    · exact ⟨i, by omega, equal⟩
    · exact Measure.span_shift out 64 4 72 (by decide) inside

theorem allocation_in_free (address capacity used : BitVec 64)
    (outcome : Serialize.Outcome (Option NatOperand))
    (geometry : TraceGeometry (arenaState address capacity used) outcome)
    (bound : address.toNat + capacity.toNat ≤ 2^64)
    (a : BitVec 64) (written : AllocationWrites outcome.calls a) :
    Codec.InSpan a (address + used) (capacity.toNat - used.toNat) := by
  have location := geometry.writes a written
  have upper := geometry.upper
  change address.toNat + used.toNat ≤ a.toNat ∧
    a.toNat < address.toNat + outcome.used at location
  change outcome.used ≤ capacity.toNat at upper
  refine ⟨a.toNat - (address.toNat + used.toNat), by omega, ?_⟩
  bv_omega

theorem writable_mutable (original : MachineData) (desc : SszNative.Codec.Desc)
    (address capacity used : BitVec 64) (bytes : Nat)
    (bound : address.toNat + capacity.toNat ≤ 2^64) (usedBound : used.toNat ≤ capacity.toNat)
    (a : BitVec 64)
    (write : Writable original bytes (FixedSize.measureFixed desc (arenaState address capacity used)) a) :
    Mutable original address used capacity bytes a := by
  rcases write with result | stack | allocation | cursor
  · exact Or.inl (result_writes_span _ _ _ result)
  · exact Or.inr (Or.inl stack)
  · exact Or.inr (Or.inr (Or.inr (allocation_in_free address capacity used _
      (measureFixed_trace_geometry desc _ bound usedBound) bound a allocation)))
  · exact Or.inr (Or.inr (Or.inl cursor.2))

/-- Publication cannot clobber the actual six-save image or original RET word. -/
theorem saved_output_safe {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (i : Nat) (hi : i < 56) :
    ¬ Codec.InSpan (body.regs.rsp.toBitVec + 88#64 + BitVec.ofNat 64 i)
      original.regs.rdi.toBitVec 72 := by
  intro inside
  have atOutput := span_bounds owned.output_bound inside
  have low := owned.stack.lowEnough
  have enough := Nat.le_trans (stackBytes_activation desc) owned.enough
  have bound := owned.return_bound
  have sp := pending.sp
  have atStack : original.regs.rsp.toNat - bytes ≤
      (body.regs.rsp.toBitVec + 88#64 + BitVec.ofNat 64 i).toNat ∧
      (body.regs.rsp.toBitVec + 88#64 + BitVec.ofNat 64 i).toNat < original.regs.rsp.toNat + 8 := by
    bv_omega
  have apart := owned.output_stack.nonempty (by decide) (by omega)
  omega

end SszX86.CodecMeasureFixed.Output
