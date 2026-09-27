import SszX86.NatAddCarryPair

namespace SszX86.NatAdd.Carry.Pair
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def headState (s : MachineData) (right : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (get s .r10) 8 (get s .rdx + right).toInt
    regs := {s.regs with
      rsi := 1
      rbx := UInt64.ofBitVec (get s .rbx + 8#64)
      rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++ 1#8)
      r9 := UInt64.ofBitVec (get s .rdx + right)
      r11 := UInt64.ofBitVec (get s .r11 &&& get s .rax)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 (Udivti3.addFlags (get s .rdx) right).cf.toNat)
      r15 := UInt64.ofBitVec right}
    status := flags}

/-- The real Small/Large dispatch reaches the paired body only after executing
its first store, count check, even-count mask and output-pointer adjustment. -/
theorem small_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (right : BitVec 64)
    (hleft : get s .rsi = 0) (hpointer : get s .rcx ≠ 0)
    (hlength : get s .r8 ≠ 0) (hcount : get s .rax ≠ 1#64)
    (hright : Mem.loadInt s.dmem (get s .rcx) 8 = some (right.toNat : Int))
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (headState s right flags, base+1252)) :
    Eventually (step e) P (s, base+536) := by
  have t862 := hc.targets ("natAdd_u862", 862) (by decide)
  have t1080 := hc.targets ("natAdd_u1080", 1080) (by decide)
  have t914 := hc.targets ("natAdd_u914", 914) (by decide)
  have t1060 := hc.targets ("natAdd_u1060", 1060) (by decide)
  have t1207 := hc.targets ("natAdd_u1207", 1207) (by decide)
  repeat' ((first
    | solve | simpa [headState, get, Udivti3.addFlags, StatusFlags.from_result,
        BitVec.ofInt_toInt, BitVec.ofInt_add, BitVec.add_assoc] using hp _
    | solve | simpa [get] using hm
    | apply And.intro
    | apply Delimited.store_cps
    | natadd_step 138 using hc
    | natadd_step 139 using hc
    | natadd_step 219 using hc
    | natadd_step 220 using hc
    | natadd_step 221 using hc
    | natadd_step 222 using hc
    | natadd_step 223 using hc
    | natadd_step 228 using hc
    | natadd_step 229 using hc
    | natadd_step 230 using hc
    | natadd_step 231 using hc
    | natadd_step 238 using hc
    | natadd_step 239 using hc
    | natadd_step 240 using hc
    | natadd_step 241 using hc
    | natadd_step 242 using hc
    | natadd_step 243 using hc
    | natadd_step 277 using hc
    | natadd_step 278 using hc
    | natadd_step 315 using hc
    | natadd_step 316 using hc
    | natadd_step 317 using hc
    | natadd_step 318 using hc) <;>
    try simp (config := {instances := true}) [StatusFlags.from_result,
      Udivti3.zf_sub, get, hleft, hpointer, hlength, hcount,
      t862, t1080, t914, t1060, t1207, Effects.All, MachineData.load,
      Width.bytes, Width.bits, hright, Delimited.word_cast,
      BitVec.ofInt_add, BitVec.ofInt_toInt])

end SszX86.NatAdd.Carry.Pair
