import SszX86.CodecEmitSteps
import SszX86.CodecEmitTable
import SszX86.EmitMemcpyCallMemory

namespace SszX86.CodecEmit
open UintCodec
/-- Exact argument shuffle before emit_parts. Its seventh argument is the
original output length, stored in the caller's first local stack word. -/
def partsCallState (s : MachineData) (values count : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec values
      rcx := UInt64.ofBitVec count
      rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 32)
      rdi := s.regs.rbx
      r9 := s.regs.r14}
    dmem := Mem.storeInt s.dmem s.regs.rsp.toBitVec 8 s.regs.r9.toBitVec.toInt}

theorem parts_args_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (values count : BitVec 64) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8) 8 = some (values.toNat : Int))
    (length : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (count.toNat : Int))
    (hm : Large.Mapped s.dmem s.regs.rsp.toBitVec 8)
    (next : Eventually (step e) P (partsCallState s values count, base + 1265)) :
    Eventually (step e) P (s, base + 1240) := by
  codec_emit_step 304 using code
  codec_emit_load pointer
  codec_emit_step 305 using code
  codec_emit_load length
  codec_emit_step 306 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem s.regs.rsp.toBitVec 8 0 8 hm (by decide)
  simp only [Effects.All]
  codec_emit_step 307 using code
  codec_emit_step 308 using code
  codec_emit_step 309 using code
  simpa [partsCallState, Effects.All] using next

/-- The linked helper entry is root+1712, after the actual CALL continuation
root+1270 is committed in the eight-byte return slot. -/
theorem parts_call_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (Emit.callState s (base + 1270).toBitVec, base + 1712)) :
    Eventually (step e) P (s, base + 1265) := by
  codec_emit_step 310 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 hm (by decide)
  simpa [Emit.callState, Effects.All, Int64.add_assoc] using next

/-- The helper already publishes the result; the root only branches to its
actual epilogue and does not initialize any additional sret payload. -/
theorem parts_return_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, base + 1600)) :
    Eventually (step e) P (s, base + 1270) := by
  codec_emit_step 311 using code
  simpa only [Effects.All, Int64.add_assoc] using next

def repeatedPartsState (s : MachineData) (child : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec child}
    dmem := Mem.storeInt
      (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 40) 8 child.toInt)
      (s.regs.rsp.toBitVec + 32) 8 0}

/-- Repeated descriptors construct the actual two-word Parts niche: first word
zero, second word borrowed child pointer. No heap allocation is performed. -/
theorem repeated_parts_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (child : BitVec 64) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec) 8 =
      some (child.toNat : Int))
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec + 32) 16)
    (next : Eventually (step e) P (repeatedPartsState s child, base + 1240)) :
    Eventually (step e) P (s, base + 1196) := by
  have second : Large.Mapped s.dmem (s.regs.rsp.toBitVec + 40) 8 := by
    have h := Delimited.Reservation.mapped_subrange s.dmem (s.regs.rsp.toBitVec + 32)
      16 8 8 hm (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, show (32#64 + 8#64) = 40#64 by decide]
      using h
  codec_emit_step 295 using code
  codec_emit_load pointer
  codec_emit_step 296 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec + 40) 8 0 8 second (by decide)
  simp only [Effects.All]
  codec_emit_step 297 using code
  apply Delimited.store_cps
  · have extended := Large.mapped_store s.dmem (s.regs.rsp.toBitVec + 32)
      (s.regs.rsp.toBitVec + 40) 16 8 child.toInt hm
    simpa only [BitVec.add_zero] using
      Large.mapped_load _ (s.regs.rsp.toBitVec + 32) 16 0 8 extended (by decide)
  simp only [Effects.All]
  codec_emit_step 298 using code
  simpa only [repeatedPartsState, Effects.All, Int64.add_assoc] using next

def fieldsPartsState (s : MachineData) (fields count : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec count
      rcx := UInt64.ofBitVec fields}
    dmem := Mem.storeInt
      (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 32) 8 fields.toInt)
      (s.regs.rsp.toBitVec + 40) 8 count.toInt}

/-- Fields retain the original physical slice, including its empty nonnull
pointer. No allocation, field-name read, or descriptor validation occurs here. -/
theorem fields_parts_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (fields count : BitVec 64) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec) 8 =
      some (fields.toNat : Int))
    (length : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec + 8) 8 =
      some (count.toNat : Int))
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec + 32) 16)
    (next : Eventually (step e) P (fieldsPartsState s fields count, base + 1240)) :
    Eventually (step e) P (s, base + 1221) := by
  codec_emit_step 300 using code
  codec_emit_load pointer
  codec_emit_step 301 using code
  codec_emit_load length
  codec_emit_step 302 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec + 32) 16 0 8 hm (by decide)
  simp only [Effects.All]
  codec_emit_step 303 using code
  apply Delimited.store_cps
  · have extended := Large.mapped_store s.dmem (s.regs.rsp.toBitVec + 32)
      (s.regs.rsp.toBitVec + 32) 16 8 fields.toInt hm
    have second := Large.mapped_load _ (s.regs.rsp.toBitVec + 32) 16 8 8 extended (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      show (32#64 + 8#64) = 40#64 by decide] using second
  simpa only [fieldsPartsState, Effects.All] using next

def PartsKind.payloadOffset : PartsKind → Nat
  | .vector | .list | .progressiveContainer => 24
  | .progressiveList | .container => 8

def PartsKind.payloadPC : PartsKind → Nat
  | .vector | .list | .progressiveList => 1196
  | .container | .progressiveContainer => 1221

def payloadState (s : MachineData) (kind : PartsKind) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat kind.payloadOffset}}

/-- The second table's destination executes the exact descriptor payload
offset selection before a borrowed child pointer or fields slice is loaded. -/
theorem parts_payload_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (kind : PartsKind) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (payloadState s kind, base + Int64.ofNat kind.payloadPC)) :
    Eventually (step e) P (s, base + Int64.ofNat kind.entry) := by
  cases kind with
  | vector =>
    codec_emit_step 76 using code
    codec_emit_step 77 using code
    simpa [payloadState, PartsKind.payloadOffset, PartsKind.payloadPC, Effects.All] using next
  | list =>
    codec_emit_step 76 using code
    codec_emit_step 77 using code
    simpa [payloadState, PartsKind.payloadOffset, PartsKind.payloadPC, Effects.All] using next
  | progressiveList =>
    codec_emit_step 294 using code
    simpa [payloadState, PartsKind.payloadOffset, PartsKind.payloadPC, Effects.All] using next
  | container =>
    codec_emit_step 299 using code
    simpa [payloadState, PartsKind.payloadOffset, PartsKind.payloadPC, Effects.All] using next
  | progressiveContainer =>
    codec_emit_step 292 using code
    codec_emit_step 293 using code
    simpa [payloadState, PartsKind.payloadOffset, PartsKind.payloadPC, Effects.All] using next

end SszX86.CodecEmit
