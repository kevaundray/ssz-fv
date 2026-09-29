import SszX86.CodecBoundedExec

namespace SszX86.CodecBounded
open SszX86.UintCodec
open SszNative

macro "codec_bound_output " row:num " offset " off:num " width " width:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $width))
  else
    `(tactic| apply Large.mapped_load (capacity := 68) (offset := $off) («width» := $width))
  `(tactic|
    (codec_bound_step $row using $hc
     simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def errorPayload (m : DataMem) (out cp cv ap av : BitVec 64) : DataMem :=
  let m := Mem.storeInt m out 8 1
  let m := Mem.storeInt m (out + 8#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 cp.toInt
  let m := Mem.storeInt m (out + 24#64) 8 cv.toInt
  let m := Mem.storeInt m (out + 32#64) 8 ap.toInt
  let m := Mem.storeInt m (out + 40#64) 8 av.toInt
  let m := Mem.storeInt m (out + 48#64) 8 0
  Mem.storeInt m (out + 56#64) 8 0

def rejected (s : MachineData) (actual : NatOperand) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec actual.pointer
      rcx := UInt64.ofBitVec actual.payload
      rbp := 2}
    dmem := errorPayload s.dmem s.regs.rbx.toBitVec s.regs.r15.toBitVec
      s.regs.r12.toBitVec actual.pointer actual.payload}

/-- Actual Nat metadata is reloaded after the first four error stores. -/
theorem reject_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (actual : NatOperand)
    (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 68)
    (ap : Mem.loadInt s.dmem s.regs.r14.toBitVec 8 = some (actual.pointer.toNat : Int))
    (av : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 8#64) 8 = some (actual.payload.toNat : Int))
    (apart : ∀ i < 16, ∀ j < 68,
      s.regs.r14.toBitVec + BitVec.ofNat 64 i ≠ s.regs.rbx.toBitVec + BitVec.ofNat 64 j)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (rejected s actual, base + 110)) :
    Eventually (step e) P (s, base + 51) := by
  have keep (m : DataMem) (a b : Nat) (v : Int) (ha : a + 8 ≤ 16) (hb : b + 8 ≤ 68) :
      Mem.loadInt (Mem.storeInt m (s.regs.rbx.toBitVec + BitVec.ofNat 64 b) 8 v)
        (s.regs.r14.toBitVec + BitVec.ofNat 64 a) 8 =
        Mem.loadInt m (s.regs.r14.toBitVec + BitVec.ofNat 64 a) 8 := by
    apply BoolCodec.load_store_disjoint
    intro i hi j hj
    simp only [memmove_addr_add]
    exact apart (a+i) (by omega) (b+j) (by omega)
  have keep0 (m : DataMem) (a : Nat) (v : Int) (ha : a + 8 ≤ 16) :
      Mem.loadInt (Mem.storeInt m s.regs.rbx.toBitVec 8 v)
        (s.regs.r14.toBitVec + BitVec.ofNat 64 a) 8 =
        Mem.loadInt m (s.regs.r14.toBitVec + BitVec.ofNat 64 a) 8 := by
    simpa using keep m a 0 v ha (by decide)
  have keepAt0 (m : DataMem) (b : Nat) (v : Int) (hb : b + 8 ≤ 68) :
      Mem.loadInt (Mem.storeInt m (s.regs.rbx.toBitVec + BitVec.ofNat 64 b) 8 v)
        s.regs.r14.toBitVec 8 = Mem.loadInt m s.regs.r14.toBitVec 8 := by
    simpa using keep m 0 b v (by decide) hb
  have keepBoth0 (m : DataMem) (v : Int) :
      Mem.loadInt (Mem.storeInt m s.regs.rbx.toBitVec 8 v) s.regs.r14.toBitVec 8 =
        Mem.loadInt m s.regs.r14.toBitVec 8 := by simpa using keep m 0 0 v (by decide) (by decide)
  codec_bound_output 19 offset 0 width 8 using hc mapped mapped
  codec_bound_output 20 offset 8 width 8 using hc mapped mapped
  codec_bound_output 21 offset 16 width 8 using hc mapped mapped
  codec_bound_output 22 offset 24 width 8 using hc mapped mapped
  codec_bound_step 23 using hc
  simp (disch := decide) only [keepAt0, keepBoth0]
  codec_bound_load ap
  codec_bound_step 24 using hc
  simp (disch := decide) only [keep, keep0]
  codec_bound_load av
  codec_bound_output 25 offset 32 width 8 using hc mapped mapped
  codec_bound_output 26 offset 40 width 8 using hc mapped mapped
  codec_bound_output 27 offset 48 width 8 using hc mapped mapped
  codec_bound_output 28 offset 56 width 8 using hc mapped mapped
  codec_bound_step 29 using hc
  simpa [rejected, errorPayload] using next

def published (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 64#64) 4
    (s.regs.rbp.toBitVec.setWidth 32).toInt}

theorem publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 68)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (published s, base + 113)) :
    Eventually (step e) P (s, base + 110) := by
  codec_bound_output 30 offset 64 width 4 using hc mapped mapped
  simpa [published] using next

structure SavedAt (m : DataMem) (sp : BitVec 64) (original : MachineData) (ra : BitVec 64) : Prop where
  rbx : Mem.loadInt m sp 8 = some (Int.ofBytes (wordBytes original.regs.rbx.toBitVec))
  r12 : Mem.loadInt m (sp + 8) 8 = some (Int.ofBytes (wordBytes original.regs.r12.toBitVec))
  r14 : Mem.loadInt m (sp + 16) 8 = some (Int.ofBytes (wordBytes original.regs.r14.toBitVec))
  r15 : Mem.loadInt m (sp + 24) 8 = some (Int.ofBytes (wordBytes original.regs.r15.toBitVec))
  rbp : Mem.loadInt m (sp + 32) 8 = some (Int.ofBytes (wordBytes original.regs.rbp.toBitVec))
  ret : Mem.loadInt m (sp + 40) 8 = some (Int.ofBytes (wordBytes ra))

def restored (s original : MachineData) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := original.regs.rbx
      r12 := original.regs.r12
      r14 := original.regs.r14
      r15 := original.regs.r15
      rbp := original.regs.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 48)}}

/-- Five POPs followed by RET; their bytes are observed, not presumed restored. -/
theorem restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (ra : BitVec 64)
    (saved : SavedAt s.dmem s.regs.rsp.toBitVec original ra)
    (P : MachineState → Prop)
    (next : P (restored s original, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 113) := by
  codec_bound_step 31 using hc
  simp only [MachineData.load, Effects.All, saved.rbx, ofBytes_wordBytes]
  codec_bound_step 32 using hc
  simp only [MachineData.load, Effects.All, saved.r12, ofBytes_wordBytes]
  codec_bound_step 33 using hc
  simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
    saved.r14, ofBytes_wordBytes]
  codec_bound_step 34 using hc
  simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
    saved.r15, ofBytes_wordBytes]
  codec_bound_step 35 using hc
  simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
    saved.rbp, ofBytes_wordBytes]
  codec_bound_step 36 using hc
  simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
    saved.ret, ofBytes_wordBytes]
  simpa [restored, BitVec.add_assoc, UInt64.add_assoc] using Eventually.done _ next

end SszX86.CodecBounded
