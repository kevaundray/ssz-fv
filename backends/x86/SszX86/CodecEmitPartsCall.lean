import SszX86.CodecEmitPartsSteps
import SszX86.EmitMemcpyCallMemory

namespace SszX86.CodecEmitParts
open UintCodec

/-- These are the four real recursive emitter calls in the native parts loops. -/
inductive EmitSite where
  | fixedHead | variableBody | sequentialField | sequentialRepeated

def EmitSite.pc : EmitSite → Nat
  | .fixedHead => 406
  | .variableBody => 533
  | .sequentialField => 660
  | .sequentialRepeated => 773

def EmitSite.next : EmitSite → Nat
  | .fixedHead => 411
  | .variableBody => 538
  | .sequentialField => 665
  | .sequentialRepeated => 778

/-- Instruction-local CPS, not a recursive helper contract: the CALL first
stores its own exact continuation. The eventual recursive theorem supplies this
continuation by strict value-child induction. -/
theorem emit_call_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (site : EmitSite) (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (Emit.callState s (base + Int64.ofNat site.next).toBitVec, base - 1712)) :
    Eventually (step e) P (s, base + Int64.ofNat site.pc) := by
  have slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 mapped (by decide)
  cases site with
  | fixedHead =>
    codec_parts_step 99 using code
    apply Delimited.store_cps
    · exact slot
    simpa [Emit.callState, EmitSite.pc, EmitSite.next, Effects.All, Int64.add_assoc] using next
  | variableBody =>
    codec_parts_step 126 using code
    apply Delimited.store_cps
    · exact slot
    simpa [Emit.callState, EmitSite.pc, EmitSite.next, Effects.All, Int64.add_assoc] using next
  | sequentialField =>
    codec_parts_step 156 using code
    apply Delimited.store_cps
    · exact slot
    simpa [Emit.callState, EmitSite.pc, EmitSite.next, Effects.All, Int64.add_assoc] using next
  | sequentialRepeated =>
    codec_parts_step 185 using code
    apply Delimited.store_cps
    · exact slot
    simpa [Emit.callState, EmitSite.pc, EmitSite.next, Effects.All, Int64.add_assoc] using next

/-- The fixed/variable classification of fields is an actual linked CALL, not a
semantic oracle. Its continuation and eight-byte push are explicit. -/
theorem is_fixed_call_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (Emit.callState s (base + 338).toBitVec, base + 1088)) :
    Eventually (step e) P (s, base + 333) := by
  have slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 mapped (by decide)
  codec_parts_step 81 using code
  apply Delimited.store_cps
  · exact slot
  simpa [Emit.callState, Effects.All, Int64.add_assoc] using next

end SszX86.CodecEmitParts
