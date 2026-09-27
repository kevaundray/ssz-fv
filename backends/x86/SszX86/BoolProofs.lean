import SszX86.BoolStores
import SszX86.BoolReturn

namespace SszX86.BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The caller's result object does not overlap the saved activation record. -/
def StackSeparated (out sp : BitVec 64) : Prop :=
  ∀ j < 56, ∀ i < 80,
    sp + BitVec.ofNat 64 (312 + j) ≠ out + BitVec.ofNat 64 i

def decodedMem (m : DataMem) (out length : BitVec 64) (byte : BitVec 8) : DataMem :=
  if length = 1#64 then
    if byte = 0#8 then successMem m out false
    else if byte = 1#8 then successMem m out true
    else badMem m out (byte.setWidth 64)
  else scopeMem m out length

theorem decoded_frame (m : DataMem) (out length address : BitVec 64) (byte : BitVec 8)
    (ha : ∀ i < 80, address ≠ out + BitVec.ofNat 64 i) :
    (decodedMem m out length byte).get? address = m.get? address := by
  have he : ∀ i < 76, address ≠ out + BitVec.ofNat 64 i := fun i hi => ha i (by omega)
  have ht : ∀ i < 8, address ≠ out + BitVec.ofNat 64 i := fun i hi => ha i (by omega)
  have hv : ∀ i < 2, address ≠ out + 16#64 + BitVec.ofNat 64 i := by
    intro i hi
    simpa only [memmove_addr_add] using ha (16 + i) (by omega)
  unfold decodedMem
  split
  · split
    · exact success_frame m out address false ht hv
    · split
      · exact success_frame m out address true ht hv
      · exact bad_frame m out address (byte.setWidth 64) he
  · exact scope_frame m out address length he

private theorem saved_load_congr (m m' : DataMem) (sp : BitVec 64)
    (h : ∀ i < 56, m'.get? (sp + BitVec.ofNat 64 (312 + i)) =
      m.get? (sp + BitVec.ofNat 64 (312 + i)))
    (offset : Nat) (hb : offset + 8 ≤ 56) :
    Mem.loadInt m' (sp + BitVec.ofNat 64 (312 + offset)) 8 =
      Mem.loadInt m (sp + BitVec.ofNat 64 (312 + offset)) 8 := by
  apply memmove_loadInt_congr
  intro i hi
  rw [memmove_addr_add]
  simpa only [Nat.add_assoc] using h (offset + i) (by omega)

theorem savedAt_congr (m m' : DataMem) (sp : BitVec 64) (saved : Saved)
    (h : ∀ i < 56, m'.get? (sp + BitVec.ofNat 64 (312 + i)) =
      m.get? (sp + BitVec.ofNat 64 (312 + i)))
    (hs : SavedAt m sp saved) : SavedAt m' sp saved := by
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨(saved_load_congr m m' sp h 0 (by decide)).trans h0,
    (saved_load_congr m m' sp h 8 (by decide)).trans h1,
    (saved_load_congr m m' sp h 16 (by decide)).trans h2,
    (saved_load_congr m m' sp h 24 (by decide)).trans h3,
    (saved_load_congr m m' sp h 32 (by decide)).trans h4,
    (saved_load_congr m m' sp h 40 (by decide)).trans h5,
    (saved_load_congr m m' sp h 48 (by decide)).trans h6⟩

theorem decoded_saved (m : DataMem) (out length sp : BitVec 64) (byte : BitVec 8)
    (saved : Saved) (hsep : StackSeparated out sp) (hs : SavedAt m sp saved) :
    SavedAt (decodedMem m out length byte) sp saved := by
  apply savedAt_congr m _ sp saved _ hs
  intro i hi
  exact decoded_frame m out length _ byte (hsep i hi)

/-- Exact returned state; only a unit-length input changes the byte register. -/
def decoded (s : MachineData) (saved : Saved) (byte : BitVec 8) : MachineData :=
  returned {s with
    regs := {s.regs with rax :=
      if s.regs.r14.toBitVec = 1#64 then UInt64.ofBitVec (byte.setWidth 64) else s.regs.rax}
    dmem := decodedMem s.dmem s.regs.rdi.toBitVec s.regs.r14.toBitVec byte} saved

private theorem byte_low32_nat (byte : BitVec 8) :
    ((byte.setWidth 64).extractLsb' 0 32).toNat = byte.toNat := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth_of_le (by decide),
    Nat.shiftRight_zero, Nat.mod_eq_of_lt (by have h := byte.isLt; omega)]

private theorem byte_zero (byte : BitVec 8) :
    (byte.setWidth 64).extractLsb' 0 32 = 0#32 ↔ byte = 0#8 := by
  simp only [← BitVec.toNat_inj, byte_low32_nat]
  rfl

private theorem byte_one (byte : BitVec 8) :
    (byte.setWidth 64).extractLsb' 0 32 = 1#32 ↔ byte = 1#8 := by
  simp only [← BitVec.toNat_inj, byte_low32_nat]
  rfl

/-- Every actual postdispatch instruction through RET. No input read is required
when length differs from one; output may alias the already-read input byte. -/
theorem body_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (byte : BitVec 8)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (hsep : StackSeparated s.regs.rdi.toBitVec s.regs.rsp.toBitVec)
    (hbyte : s.regs.r14.toBitVec = 1#64 →
      Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 = some (byte.toNat : Int))
    (P : MachineState → Prop)
    (hp : P (decoded s saved byte, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 45) := by
  have savedAfter := decoded_saved s.dmem s.regs.rdi.toBitVec s.regs.r14.toBitVec
    s.regs.rsp.toBitVec byte saved hsep hs
  apply length_branch e base hc s P
  by_cases hl : s.regs.r14.toBitVec = 1#64
  · simp only [beq_iff_eq, hl, ↓reduceIte]
    apply byte_load e base hc (lengthCompared s) byte P
    · exact hbyte hl
    apply byte_zero_branch
    · exact hc
    intro af
    have zero :
        (byteLoaded (lengthCompared s) byte).regs.rax.toBitVec.take 32 = 0#32 ↔
          byte = 0#8 := by
      exact byte_zero byte
    simp only [beq_iff_eq, zero]
    by_cases hz : byte = 0#8
    · simp only [hz, ↓reduceIte]
      refine success_stores e base hc _ ?_ false P ?_
      · exact hm
      refine epilogue e base hc _ saved ?_ P ?_
      · simpa [decodedMem, hl, hz, lengthCompared, byteLoaded, byteTested] using savedAfter
      · simpa [decoded, decodedMem, returned, hl, hz,
          lengthCompared, byteLoaded, byteTested] using hp
    · simp only [hz, ↓reduceIte]
      apply byte_one_branch
      · exact hc
      have one :
          (byteTested (byteLoaded (lengthCompared s) byte) af).regs.rax.toBitVec.take 32 = 1#32 ↔
            byte = 1#8 := by
        exact byte_one byte
      simp only [beq_iff_eq, one]
      by_cases ho : byte = 1#8
      · simp only [ho, ↓reduceIte]
        refine success_stores e base hc _ ?_ true P ?_
        · exact hm
        refine epilogue e base hc _ saved ?_ P ?_
        · simpa [decodedMem, hl, hz, ho, lengthCompared, byteLoaded, byteTested, byteCompared]
            using savedAfter
        · simpa [decoded, decodedMem, returned, hl, hz, ho,
            lengthCompared, byteLoaded, byteTested, byteCompared] using hp
      · simp only [ho, ↓reduceIte]
        refine bad_stores e base hc _ ?_ P ?_
        · exact hm
        refine epilogue e base hc _ saved ?_ P ?_
        · simpa [decodedMem, hl, hz, ho, lengthCompared, byteLoaded, byteTested, byteCompared]
            using savedAfter
        · simpa [decoded, decodedMem, returned, hl, hz, ho,
            lengthCompared, byteLoaded, byteTested, byteCompared] using hp
  · simp only [beq_iff_eq, hl, ↓reduceIte]
    refine scope_stores e base hc _ ?_ P ?_
    · exact hm
    refine epilogue e base hc _ saved ?_ P ?_
    · simpa [decodedMem, hl, lengthCompared] using savedAfter
    · simpa [decoded, decodedMem, returned, hl, lengthCompared] using hp

theorem decoded_result (m : DataMem) (out length : BitVec 64) (byte : UInt8)
    (hb : out.toNat + 80 ≤ 2^64) :
    SszNative.BoolCodec.ResultAt (observe (decodedMem m out length byte.toBitVec) out)
      (SszNative.BoolCodec.outcome length.toNat byte) := by
  by_cases hl : length = 1#64
  · by_cases hz : byte = 0
    · simpa [decodedMem, SszNative.BoolCodec.outcome, hl, hz]
        using success_result m out false hb
    · by_cases ho : byte = 1
      · simpa [decodedMem, SszNative.BoolCodec.outcome, hl, ho]
          using success_result m out true hb
      · have hz' : byte.toBitVec ≠ 0#8 := by
          intro h
          apply hz
          simpa using congrArg UInt8.ofBitVec h
        have ho' : byte.toBitVec ≠ 1#8 := by
          intro h
          apply ho
          simpa using congrArg UInt8.ofBitVec h
        have packed : (byte.toBitVec.setWidth 64).toNat = byte.toNat := by
          change (byte.toBitVec.setWidth 64).toNat = byte.toBitVec.toNat
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
            (by have h := byte.toBitVec.isLt; omega)]
        simpa [decodedMem, SszNative.BoolCodec.outcome, hl, hz, ho, hz', ho', packed]
          using bad_result m out (byte.toBitVec.setWidth 64) hb
  · have hn : length.toNat ≠ 1 := by
      intro h
      apply hl
      apply BitVec.eq_of_toNat_eq
      simpa using h
    simpa [decodedMem, SszNative.BoolCodec.outcome, hl, hn]
      using scope_result m out length hb

/-- Refinement of the bound postdispatch Boolean body to pinned SSZ decoding,
including actual return and the exact final machine state. Dispatch is separate. -/
theorem body_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (data : Ssz.Bytes)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (hout : s.regs.rdi.toBitVec.toNat + 80 ≤ 2^64)
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (hsep : StackSeparated s.regs.rdi.toBitVec s.regs.rsp.toBitVec)
    (hlen : s.regs.r14.toBitVec.toNat = data.size)
    (hdata : data.size = 1 →
      Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 = some (data[0]!.toNat : Int)) :
    Eventually (step e) (fun t =>
      t.2 = Int64.ofBitVec saved.rip ∧
      SszNative.BoolCodec.ResultAt (observe t.1.dmem s.regs.rdi.toBitVec)
        (Ssz.deserialize .bool data) ∧
      t.1 = decoded s saved data[0]!.toBitVec) (s, base + 45) := by
  apply body_runs e base hc s saved data[0]!.toBitVec hm hs hsep
  · intro hl
    have hd : data.size = 1 := by rw [← hlen, hl]; rfl
    simpa using hdata hd
  · refine ⟨rfl, ?_, rfl⟩
    apply SszNative.BoolCodec.result_refines
    simpa [decoded, returned, hlen] using
      decoded_result s.dmem s.regs.rdi.toBitVec s.regs.r14.toBitVec data[0]! hout

end SszX86.BoolCodec
