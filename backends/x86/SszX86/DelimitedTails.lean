import SszX86.DelimitedEarly

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def successMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 16) 1 3
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 32) 8 s.regs.rdx.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 40) 8 s.regs.rcx.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 48) 8 s.regs.r14.toBitVec.toInt
  Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 56) 8 s.regs.rbp.toBitVec.toInt

def successReady (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := successMem s
    regs := {s.regs with rax := 0}
    status := flags}

theorem success_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (successReady s flags, base + 823)) :
    Eventually (step e) P (s, base + 555) := by
  delimited_output 130 at 16 width 1 using hc mapped hm
  delimited_output 131 at 32 width 8 using hc mapped hm
  delimited_output 132 at 40 width 8 using hc mapped hm
  delimited_output 133 at 48 width 8 using hc mapped hm
  delimited_output 134 at 56 width 8 using hc mapped hm
  delimited_step 135 using hc
  constructor <;> delimited_step 136 using hc
  all_goals simpa [successReady, successMem] using hp _

def scratchMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 32) 8 0
  Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 24) 8 0

def scratchReady (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := scratchMem s
    regs := {s.regs with rax := 32768, rcx := 16, rsi := 1, rdx := 8, r15 := 0}
    status := flags}

theorem scratch_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (scratchReady s flags, base + 807)) :
    Eventually (step e) P (s, base + 736) := by
  delimited_output 160 at 64 width 8 using hc mapped hm
  delimited_output 161 at 56 width 8 using hc mapped hm
  delimited_output 162 at 48 width 8 using hc mapped hm
  delimited_output 163 at 40 width 8 using hc mapped hm
  delimited_output 164 at 32 width 8 using hc mapped hm
  delimited_output 165 at 24 width 8 using hc mapped hm
  delimited_step 166 using hc
  delimited_step 167 using hc
  delimited_step 168 using hc
  delimited_step 169 using hc
  delimited_step 170 using hc
  constructor <;> simpa [scratchReady, scratchMem] using hp _

def errorTailMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec) 8 s.regs.rsi.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + s.regs.rcx.toBitVec) 8 s.regs.r15.toBitVec.toInt
  Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 72) 4
    (s.regs.rax.toBitVec.setWidth 32).toInt

def errorTailReady (s : MachineData) : MachineData :=
  {s with dmem := errorTailMem s, regs := {s.regs with rax := 1}}

/-- The shared error tail stores either the scratch header or the actual Nat,
according to the two constant offsets prepared by the preceding branch. -/
theorem error_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s)
    (hd : s.regs.rdx.toNat + 8 ≤ 76) (hc' : s.regs.rcx.toNat + 8 ≤ 76)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (errorTailReady s, base + 823)) :
    Eventually (step e) P (s, base + 807) := by
  delimited_step 171 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      UintCodec.Large.mapped_load s.dmem s.regs.rdi.toBitVec 76 s.regs.rdx.toNat 8 hm hd
  simp only [Effects.All]
  delimited_step 172 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      UintCodec.Large.mapped_load _ s.regs.rdi.toBitVec 76 s.regs.rcx.toNat 8
        (UintCodec.Large.mapped_store _ _ _ _ _ _ hm) hc'
  simp only [Effects.All]
  delimited_output 173 at 72 width 4 using hc mapped hm
  delimited_step 174 using hc
  simpa [errorTailReady, errorTailMem] using hp

def tagged (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem s.regs.rdi.toBitVec 8 s.regs.rax.toBitVec.toInt}

theorem tag_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (hp : Eventually (step e) P (tagged s, base + 840)) :
    Eventually (step e) P (s, base + 837) := by
  delimited_output 182 at 0 width 8 using hc mapped hm
  exact hp

end SszX86.Delimited
