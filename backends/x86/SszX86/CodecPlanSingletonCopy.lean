import SszX86.CodecPlanSingletonMemory

namespace SszX86.CodecPlanSingleton
open SszX86.UintCodec

def committed (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsi := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.rcx.toBitVec)}
    dmem := Mem.storeInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 s.regs.r8.toBitVec.toInt}

/-- Reservation commits before the first initializer load. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : ∃ old,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (committed s, base + 61)) :
    Eventually (step e) P (s, base + 53) := by
  codec_plan_step 17 using hc
  apply Delimited.store_cps
  · exact mapped
  · simp only [Effects.All]
    codec_plan_step 18 using hc
    simpa [committed, BitVec.ofInt_add, BitVec.ofInt_toInt] using next

def copied (s : MachineData) (w : PlanWords) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := UInt64.ofBitVec w.children
      rdx := UInt64.ofBitVec w.count}
    dmem := copyMem s.dmem (s.regs.rax.toBitVec + s.regs.rcx.toBitVec) w}

macro "codec_plan_copy_store " k:num " offset " off:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (codec_plan_step $k using $hc
   simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc]
   apply Delimited.store_cps
   · apply Large.mapped_load (capacity := 40) (offset := $off) («width» := 8)
     · repeat' first | exact $hm | apply Large.mapped_store
     · decide
   simp only [Effects.All]))

/-- Literal load/store order of the five-word Plan copy. Source storage may
alias any other read-only storage; only the initialized destination is excluded. -/
theorem copy_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (w : PlanWords)
    (input : w.At s.dmem s.regs.rdx.toBitVec)
    (mapped : Large.Mapped s.dmem (s.regs.rax.toBitVec + s.regs.rcx.toBitVec) 40)
    (apart : Apart s.regs.rdx.toBitVec 40 (s.regs.rax.toBitVec + s.regs.rcx.toBitVec) 40)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied s w, base + 104)) :
    Eventually (step e) P (s, base + 61) := by
  have keep (m : DataMem) (a b : Nat) (v : Int) (ha : a + 8 ≤ 40) (hb : b + 8 ≤ 40) :
      Mem.loadInt (Mem.storeInt m (s.regs.rax.toBitVec + s.regs.rcx.toBitVec + BitVec.ofNat 64 b) 8 v)
        (s.regs.rdx.toBitVec + BitVec.ofNat 64 a) 8 =
        Mem.loadInt m (s.regs.rdx.toBitVec + BitVec.ofNat 64 a) 8 :=
    load_store_apart m _ _ 40 40 a b 8 8 v apart ha hb
  have keep0 (m : DataMem) (b : Nat) (v : Int) (hb : b + 8 ≤ 40) :
      Mem.loadInt (Mem.storeInt m (s.regs.rax.toBitVec + s.regs.rcx.toBitVec + BitVec.ofNat 64 b) 8 v)
        s.regs.rdx.toBitVec 8 = Mem.loadInt m s.regs.rdx.toBitVec 8 := by
    simpa using keep m 0 b v (by decide) hb
  codec_plan_step 19 using hc
  codec_plan_load input.2.2.2.2
  codec_plan_copy_store 20 offset 32 using hc mapped mapped
  codec_plan_step 21 using hc
  simp (disch := decide) only [keep]
  codec_plan_load input.2.2.2.1
  codec_plan_copy_store 22 offset 24 using hc mapped mapped
  codec_plan_step 23 using hc
  simp (disch := decide) only [keep]
  codec_plan_load input.2.2.1
  codec_plan_copy_store 24 offset 16 using hc mapped mapped
  codec_plan_step 25 using hc
  simp (disch := decide) only [keep0]
  codec_plan_load input.1
  codec_plan_step 26 using hc
  simp (disch := decide) only [keep]
  codec_plan_load input.2.1
  codec_plan_copy_store 27 offset 8 using hc mapped mapped
  codec_plan_step 28 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 40) (byteCount := 8)
    · repeat' first | exact mapped | apply Large.mapped_store
    · decide
  · simpa [copied, copyMem, Effects.All, BitVec.add_assoc] using next

macro "codec_plan_output " row:num " offset " off:num " width " width:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $width))
  else
    `(tactic| apply Large.mapped_load (capacity := 68) (offset := $off) («width» := $width))
  `(tactic|
    (codec_plan_step $row using $hc
     simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def published (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := 0, rcx := 1}
    status := flags
    dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec}

theorem publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 68)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (published s flags, base + 121)) :
    Eventually (step e) P (s, base + 104) := by
  have afterZero (flags : StatusFlags) : Eventually (step e) P
      ({s with regs := {s.regs with rax := 0}, status := flags}, base + 106) := by
    codec_plan_step 30 using hc
    codec_plan_output 31 offset 0 width 8 using hc mapped mapped
    codec_plan_output 32 offset 8 width 8 using hc mapped mapped
    codec_plan_output 33 offset 64 width 4 using hc mapped mapped
    simpa [published, successMem] using next flags
  codec_plan_step 29 using hc
  constructor <;> exact afterZero _

def failed (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := 32768, rsi := 1, rcx := 0}
    status := flags
    dmem := errorMem s.dmem s.regs.rdi.toBitVec}

theorem failure_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 68)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (failed s flags, base + 192)) :
    Eventually (step e) P (s, base + 122) := by
  codec_plan_output 35 offset 56 width 8 using hc mapped mapped
  codec_plan_output 36 offset 48 width 8 using hc mapped mapped
  codec_plan_output 37 offset 40 width 8 using hc mapped mapped
  codec_plan_output 38 offset 32 width 8 using hc mapped mapped
  codec_plan_output 39 offset 24 width 8 using hc mapped mapped
  codec_plan_output 40 offset 16 width 8 using hc mapped mapped
  codec_plan_step 41 using hc
  codec_plan_step 42 using hc
  codec_plan_step 43 using hc
  constructor <;> codec_plan_output 44 offset 0 width 8 using hc mapped mapped
  all_goals codec_plan_output 45 offset 8 width 8 using hc mapped mapped
  all_goals codec_plan_output 46 offset 64 width 4 using hc mapped mapped
  all_goals simpa [failed, errorMem] using next _

theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with rsp := UInt64.ofBitVec
      (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 121) ∧
    Eventually (step e) P (s, base + 192) := by
  constructor
  · codec_plan_step 34 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · codec_plan_step 47 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next

end SszX86.CodecPlanSingleton
