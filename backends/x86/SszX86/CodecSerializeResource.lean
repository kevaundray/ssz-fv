import SszX86.CodecSerializePublish
import SszX86.SerializeEdges

namespace SszX86.CodecSerialize.Publish
open SszNative UintCodec
open SszX86.Serialize.Publish

/-- Physical ownership at either real resource-error arm, independent of the
logical descriptor, successful schema validation, or any future machine state. -/
structure ResourceOwned (s original : MachineData) (ra : BitVec 64) : Prop where
  result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72
  resultBound : s.regs.rbx.toNat + 72 ≤ 2^64
  apart : Large.Disjoint s.regs.rbx.toBitVec s.regs.rsp.toBitVec 72 144
  saved : Serialize.SavedAt s.dmem s.regs.rsp.toBitVec original
  returned : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 136) 8 =
    some (Int.ofBytes (wordBytes ra))
  stack : s.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136
  rbp : s.regs.rbp = original.regs.rbp
  vectors : s.zmms = original.zmms

def ResourcePost (s original : MachineData) (ra : BitVec 64) (t : MachineState) : Prop :=
  Measure.ABI original ra t ∧
  Codec.ErrorAt (widthLoad t.1.dmem) s.regs.rbx.toNat (.primitive .outputTooSmall) ∧
  Emit.MemoryFrame s.dmem t.1.dmem (fun a => Emit.InSpan a s.regs.rbx.toBitVec 68)

private theorem capacity_fields72 (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 72 ≤ 2^64) : TooSmallAt (capacityMem m out) out := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [capacityMem, BoolCodec.load_store_offset_disjoint, BoolCodec.load_store_same,
     Nat.reduceMul]
  all_goals decide

private theorem host_fields72 (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 72 ≤ 2^64) : TooSmallAt (hostMem m out) out := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [hostMem, BoolCodec.load_store_offset_disjoint, BoolCodec.load_store_same,
     Nat.reduceMul]
  all_goals decide

private theorem resource_finish (e : Executable) (base : Int64)
    (code : CodecSerialize.CodeAt e base) (s original : MachineData) (ra : BitVec 64)
    (owned : ResourceOwned s original ra) (memory : DataMem)
    (fields : TooSmallAt memory s.regs.rbx.toBitVec)
    (frame : Emit.MemoryFrame s.dmem memory (fun a => Emit.InSpan a s.regs.rbx.toBitVec 68)) :
    Eventually (step e) (ResourcePost s original ra) ({s with dmem := memory}, base + 410) := by
  have saved : Serialize.SavedAt memory s.regs.rsp.toBitVec original := by
    apply Serialize.savedAt_congr s.dmem memory s.regs.rsp.toBitVec original _ owned.saved
    intro i hi
    apply frame
    rintro ⟨j,hj,equal⟩
    apply owned.apart j (by omega) (96 + i) (by omega)
    bv_omega
  have returned : Mem.loadInt memory (s.regs.rsp.toBitVec + 136) 8 =
      some (Int.ofBytes (wordBytes ra)) := by
    rw [Emit.frame_load s.dmem memory _ frame]
    · exact owned.returned
    · intro i hi
      rintro ⟨j,hj,equal⟩
      apply owned.apart j (by omega) (136 + i) (by omega)
      bv_omega
  apply Serialize.epilogue_cps e base code.wrapper _ original ra saved returned
  apply Eventually.done
  have anchors := Serialize.returnedState_abi {s with dmem := memory} original
    owned.stack owned.rbp
  rcases anchors with ⟨stack,rbx,r12,r13,r14,r15,rbp⟩
  exact ⟨⟨rfl,stack,rbx,rbp,r12,r13,r14,r15,owned.vectors⟩,
    (Codec.errorAt_primitive _ _ .outputTooSmall).mpr fields.observed, frame⟩

/-- Capacity refusal executes its actual low-to-high publication and the caller's
original return. Only the active 68 bytes change; result padding is untouched. -/
theorem capacity_return (e : Executable) (base : Int64)
    (code : CodecSerialize.CodeAt e base) (s original : MachineData) (ra : BitVec 64)
    (owned : ResourceOwned s original ra) :
    Eventually (step e) (ResourcePost s original ra) (s, base + 313) := by
  apply capacity_cps e base code s owned.result
  exact resource_finish e base code s original ra owned _
    (capacity_fields72 _ _ owned.resultBound) (capacity_frame _ _)

/-- Host-size refusal keeps the real reverse store order before joining the same
native status publication and RET; arbitrary logical Nat sizes are not capped. -/
theorem host_return (e : Executable) (base : Int64)
    (code : CodecSerialize.CodeAt e base) (s original : MachineData) (ra : BitVec 64)
    (owned : ResourceOwned s original ra) :
    Eventually (step e) (ResourcePost s original ra) (s, base + 235) := by
  apply host_cps e base code s owned.result
  exact resource_finish e base code s original ra owned _
    (host_fields72 _ _ owned.resultBound) (host_frame _ _)

end SszX86.CodecSerialize.Publish
