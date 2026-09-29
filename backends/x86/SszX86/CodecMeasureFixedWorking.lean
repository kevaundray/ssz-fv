import SszX86.CodecMeasureFixedChild
import SszX86.CodecMeasureFixedOutputFinishCore
import SszX86.CodecMeasureFixedTrace

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- Current physical evidence during one fixed-measurement activation. The
cursor and ordered calls describe only the already executed prefix. -/
structure Working (original : MachineData) (base : Int64) (r : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (address capacity initialUsed ra : BitVec 64)
    (bytes : Nat) (current : BitVec 64) (calls : List (NatArithmetic.Outcome NatOperand))
    (body : MachineData) : Prop where
  resources : Owned {original with dmem := body.dmem} base r desc address capacity current ra bytes
  sp : body.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136#64
  output : body.regs.rbx.toBitVec = original.regs.rdi.toBitVec
  simd : body.zmms = original.zmms
  saved : Output.SavedAt body.dmem body.regs.rsp.toBitVec (Output.originalSaved original ra)
  mapping : BitVector.Mapping.Extends original.dmem body.dmem
  lower : initialUsed.toNat ≤ current.toNat
  locations : ∀ a, AllocationWrites calls a →
    address.toNat + initialUsed.toNat ≤ a.toNat ∧ a.toNat < address.toNat + current.toNat
  recorded : CallsAt (widthLoad body.dmem) calls
  frame : Codec.MemoryFrame original.dmem body.dmem (fun a =>
    Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨ AllocationWrites calls a ∨
    (Allocated calls ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8))

/-- Register-only basic blocks transport the same already-established resources. -/
theorem Working.registers {original before after : MachineData} {base : Int64}
    {r : Codec.Footprint} {desc : SszNative.Codec.Desc}
    {address capacity initialUsed ra current : BitVec 64} {bytes : Nat}
    {calls : List (NatArithmetic.Outcome NatOperand)}
    (working : Working original base r desc address capacity initialUsed ra bytes current calls before)
    (memory : after.dmem = before.dmem) (sp : after.regs.rsp = before.regs.rsp)
    (output : after.regs.rbx = before.regs.rbx) (simd : after.zmms = before.zmms) :
    Working original base r desc address capacity initialUsed ra bytes current calls after := by
  exact ⟨by simpa only [memory] using working.resources,
    by simpa only [sp] using working.sp,
    by simpa only [output] using working.output, simd.trans working.simd,
    by simpa only [memory, sp] using working.saved,
    by simpa only [memory] using working.mapping, working.lower,
    working.locations, by simpa only [memory] using working.recorded,
    by simpa only [memory] using working.frame⟩

/-- Closing the semantic prefix requires equality with the checked model's full
trace/cursor, never an assertion about execution of the remaining instructions. -/
theorem Working.pending {original body : MachineData} {base : Int64}
    {r : Codec.Footprint} {desc : SszNative.Codec.Desc}
    {address capacity initialUsed ra current : BitVec 64} {bytes : Nat}
    {calls : List (NatArithmetic.Outcome NatOperand)}
    (working : Working original base r desc address capacity initialUsed ra bytes current calls body)
    (cursor : current.toNat = (FixedSize.measureFixed desc (arenaState address capacity initialUsed)).used)
    (trace : calls = (FixedSize.measureFixed desc (arenaState address capacity initialUsed)).calls) :
    Output.Pending original desc address capacity initialUsed ra bytes body := by
  refine ⟨working.sp, working.output, working.simd, working.saved, ?_, ?_, ?_, ?_⟩
  · rw [working.output]
    exact working.resources.output_mapped
  · have loaded := working.resources.used_load
    simpa only [widthLoad, width_address, loaded, Option.map_some,
      Int.toNat_natCast, cursor] using
      (show (Mem.loadInt body.dmem (original.regs.rdx.toBitVec + 16) 8).map Int.toNat =
        some current.toNat by simp only [loaded, Option.map_some, Int.toNat_natCast])
  · simpa only [trace] using working.recorded
  · simpa only [Output.PrefixWrites, trace] using working.frame

end SszX86.CodecMeasureFixed
