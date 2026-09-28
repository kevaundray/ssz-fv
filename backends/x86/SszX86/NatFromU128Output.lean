import SszX86.NatFromU128Core

namespace SszX86.NatFromU128
open UintCodec

abbrev OutputMapped (s : MachineData) : Prop := Large.Mapped s.dmem s.regs.rdi.toBitVec 68
abbrev successMem := NatAdd.successMem
abbrev errorMem := NatAdd.errorMem

macro "natfrom_output " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $byteCount))
  else
    `(tactic| apply Large.mapped_load (capacity := 68)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (natfrom_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def smallState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rcx := 0}
    status := flags
    dmem := successMem s.dmem s.regs.rdi.toBitVec 0 s.regs.rsi.toBitVec}

theorem small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (zero : s.regs.rax.toBitVec = 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (smallState s flags, base + 19)) :
    Eventually (step e) P (s, base + 7) := by
  natfrom_step 3 using hc
  constructor <;> natfrom_output 4 at 0 width 8 using hc mapped hm
  all_goals natfrom_output 5 at 8 width 8 using hc mapped hm
  all_goals natfrom_output 6 at 64 width 4 using hc mapped hm
  all_goals simpa [smallState, successMem, NatAdd.successMem, NatAdd.pairMem, zero] using next _

theorem success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (zero : s.regs.rax.toBitVec = 0)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rcx.toBitVec s.regs.rsi.toBitVec},
        base + 105)) :
    Eventually (step e) P (s, base + 95) := by
  natfrom_output 30 at 0 width 8 using hc mapped hm
  natfrom_output 31 at 8 width 8 using hc mapped hm
  natfrom_output 32 at 64 width 4 using hc mapped hm
  simpa [successMem, NatAdd.successMem, NatAdd.pairMem, zero] using next

def errorState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := 32768, rcx := 1, rsi := 0}
    status := flags
    dmem := errorMem s.dmem s.regs.rdi.toBitVec}

theorem error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (errorState s flags, base + 176)) :
    Eventually (step e) P (s, base + 106) := by
  natfrom_output 34 at 56 width 8 using hc mapped hm
  natfrom_output 35 at 48 width 8 using hc mapped hm
  natfrom_output 36 at 40 width 8 using hc mapped hm
  natfrom_output 37 at 32 width 8 using hc mapped hm
  natfrom_output 38 at 24 width 8 using hc mapped hm
  natfrom_output 39 at 16 width 8 using hc mapped hm
  natfrom_step 40 using hc
  natfrom_step 41 using hc
  natfrom_step 42 using hc
  constructor <;> natfrom_output 43 at 0 width 8 using hc mapped hm
  all_goals natfrom_output 44 at 8 width 8 using hc mapped hm
  all_goals natfrom_output 45 at 64 width 4 using hc mapped hm
  all_goals simpa [errorState, errorMem, NatAdd.errorMem] using next _

/-- Each of the three real RETs reads the original caller return slot. -/
theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 19) ∧
    Eventually (step e) P (s, base + 105) ∧
    Eventually (step e) P (s, base + 176) := by
  refine ⟨?_, ?_, ?_⟩
  · natfrom_step 7 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · natfrom_step 33 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · natfrom_step 46 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next

end SszX86.NatFromU128
