import SszX86.IndicesElementTypeExec
import SszX86.CodecPlanSingletonMemory

namespace SszX86.IndicesElementType
open UintCodec

abbrev OutputMapped (s : MachineData) := Large.Mapped s.dmem s.regs.rdi.toBitVec 68

macro "indices_element_output " row:num " at " offset:num " width " bytes:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $bytes))
  else
    `(tactic| apply Large.mapped_load (capacity := 68) (offset := $offset) («width» := $bytes))
  `(tactic|
    (indices_element_step $row using $hc
     simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def boolMem (m : DataMem) (out : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m out 8 0) (out + 64#64) 4 0

def uintMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m out 8 1
  let m := Mem.storeInt m (out + 8#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 1
  Mem.storeInt m (out + 64#64) 4 0

def errorMem (m : DataMem) (out pointer payload : BitVec 64) (reason : Int) : DataMem :=
  let m := Mem.storeInt m out 8 1
  let m := Mem.storeInt m (out + 8#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 pointer.toInt
  let m := Mem.storeInt m (out + 24#64) 8 payload.toInt
  let m := Mem.storeInt m (out + 32#64) 8 0
  let m := Mem.storeInt m (out + 40#64) 8 0
  let m := Mem.storeInt m (out + 48#64) 8 0
  let m := Mem.storeInt m (out + 56#64) 8 0
  Mem.storeInt m (out + 64#64) 4 reason

theorem bool_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := boolMem s.dmem s.regs.rdi.toBitVec}, base + 75)) :
    Eventually (step e) P (s, base + 61) := by
  indices_element_output 17 at 0 width 8 using hc mapped mapped
  indices_element_output 18 at 64 width 4 using hc mapped mapped
  simpa only [boolMem] using next

theorem uint_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := uintMem s.dmem s.regs.rdi.toBitVec}, base + 120)) :
    Eventually (step e) P (s, base + 90) := by
  indices_element_output 23 at 0 width 8 using hc mapped mapped
  indices_element_output 24 at 8 width 8 using hc mapped mapped
  indices_element_output 25 at 16 width 8 using hc mapped mapped
  indices_element_output 26 at 64 width 4 using hc mapped mapped
  simpa only [uintMem] using next

theorem notSteppable_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := errorMem s.dmem s.regs.rdi.toBitVec 0 0 56}, base + 205)) :
    Eventually (step e) P (s, base + 135) := by
  indices_element_output 31 at 0 width 8 using hc mapped mapped
  indices_element_output 32 at 8 width 8 using hc mapped mapped
  indices_element_output 33 at 16 width 8 using hc mapped mapped
  indices_element_output 34 at 24 width 8 using hc mapped mapped
  indices_element_output 35 at 32 width 8 using hc mapped mapped
  indices_element_output 36 at 40 width 8 using hc mapped mapped
  indices_element_output 37 at 48 width 8 using hc mapped mapped
  indices_element_output 38 at 56 width 8 using hc mapped mapped
  indices_element_output 39 at 64 width 4 using hc mapped mapped
  simpa [errorMem] using next

theorem noSuchField_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := errorMem s.dmem s.regs.rdi.toBitVec
        s.regs.r8.toBitVec s.regs.rcx.toBitVec 57}, base + 414)) :
    Eventually (step e) P (s, base + 352) := by
  indices_element_output 83 at 0 width 8 using hc mapped mapped
  indices_element_output 84 at 8 width 8 using hc mapped mapped
  indices_element_output 85 at 16 width 8 using hc mapped mapped
  indices_element_output 86 at 24 width 8 using hc mapped mapped
  indices_element_output 87 at 32 width 8 using hc mapped mapped
  indices_element_output 88 at 40 width 8 using hc mapped mapped
  indices_element_output 89 at 48 width 8 using hc mapped mapped
  indices_element_output 90 at 56 width 8 using hc mapped mapped
  indices_element_output 91 at 64 width 4 using hc mapped mapped
  simpa only [errorMem] using next

/-- All five physical words are loaded by the native copy. Padding values are
arbitrary observations, not logical descriptor fields or initialized constants. -/
structure DescWords where
  tag : BitVec 64
  word8 : BitVec 64
  word16 : BitVec 64
  word24 : BitVec 64
  word32 : BitVec 64

def DescWords.At (words : DescWords) (m : DataMem) (p : BitVec 64) : Prop :=
  Mem.loadInt m p 8 = some (words.tag.toNat : Int) ∧
  Mem.loadInt m (p + 8#64) 8 = some (words.word8.toNat : Int) ∧
  Mem.loadInt m (p + 16#64) 8 = some (words.word16.toNat : Int) ∧
  Mem.loadInt m (p + 24#64) 8 = some (words.word24.toNat : Int) ∧
  Mem.loadInt m (p + 32#64) 8 = some (words.word32.toNat : Int)

def copyMem (m : DataMem) (out : BitVec 64) (words : DescWords) : DataMem :=
  let m := Mem.storeInt m (out + 32#64) 8 words.word32.toInt
  let m := Mem.storeInt m (out + 24#64) 8 words.word24.toInt
  let m := Mem.storeInt m (out + 16#64) 8 words.word16.toInt
  let m := Mem.storeInt m (out + 8#64) 8 words.word8.toInt
  let m := Mem.storeInt m out 8 words.tag.toInt
  Mem.storeInt m (out + 64#64) 4 0

def copied (s : MachineData) (words : DescWords) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec words.word8, rcx := UInt64.ofBitVec words.tag}
    dmem := copyMem s.dmem s.regs.rdi.toBitVec words}

macro "indices_element_copy_load " observation:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All, BitVec.ofInt_add,
      BitVec.ofInt_toInt, ($observation), Delimited.word_cast])

theorem copy_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : DescWords) (input : words.At s.dmem s.regs.rax.toBitVec)
    (mapped : OutputMapped s)
    (apart : CodecPlanSingleton.Apart s.regs.rax.toBitVec 40 s.regs.rdi.toBitVec 68)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied s words, base + 342)) :
    Eventually (step e) P (s, base + 297) := by
  have keep (m : DataMem) (a b : Nat) (v : Int) (ha : a + 8 ≤ 40) (hb : b + 8 ≤ 68) :
      Mem.loadInt (Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 b) 8 v)
        (s.regs.rax.toBitVec + BitVec.ofNat 64 a) 8 =
        Mem.loadInt m (s.regs.rax.toBitVec + BitVec.ofNat 64 a) 8 :=
    CodecPlanSingleton.load_store_apart m _ _ 40 68 a b 8 8 v apart ha hb
  have keep0 (m : DataMem) (b : Nat) (v : Int) (hb : b + 8 ≤ 68) :
      Mem.loadInt (Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 b) 8 v)
        s.regs.rax.toBitVec 8 = Mem.loadInt m s.regs.rax.toBitVec 8 := by
    simpa using keep m 0 b v (by decide) hb
  indices_element_step 68 using hc
  indices_element_copy_load input.2.2.2.2
  indices_element_output 69 at 32 width 8 using hc mapped mapped
  indices_element_step 70 using hc
  simp (disch := decide) only [keep]
  indices_element_copy_load input.2.2.2.1
  indices_element_output 71 at 24 width 8 using hc mapped mapped
  indices_element_step 72 using hc
  simp (disch := decide) only [keep]
  indices_element_copy_load input.2.2.1
  indices_element_output 73 at 16 width 8 using hc mapped mapped
  indices_element_step 74 using hc
  simp (disch := decide) only [keep0]
  indices_element_copy_load input.1
  indices_element_step 75 using hc
  simp (disch := decide) only [keep]
  indices_element_copy_load input.2.1
  indices_element_output 76 at 8 width 8 using hc mapped mapped
  indices_element_output 77 at 0 width 8 using hc mapped mapped
  indices_element_output 78 at 64 width 4 using hc mapped mapped
  simpa [copied, copyMem] using next

/-- The five original RET instructions all pop the same caller-owned slot. -/
theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 75) ∧
    Eventually (step e) P (s, base + 120) ∧
    Eventually (step e) P (s, base + 205) ∧
    Eventually (step e) P (s, base + 342) ∧
    Eventually (step e) P (s, base + 414) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · indices_element_step 19 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · indices_element_step 27 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · indices_element_step 40 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · indices_element_step 79 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · indices_element_step 92 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next

end SszX86.IndicesElementType
