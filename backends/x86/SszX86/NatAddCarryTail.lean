import SszX86.NatAddCarryPair

namespace SszX86.NatAdd.Carry.Pair
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Even count needs no further store after the final real pair. -/
theorem even_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (even : (get s .rax).extractLsb' 0 8 &&& 1#8 = 0#8)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P ({s with status := flags}, base+1325)) :
    Eventually (step e) P (s, base+1297) := by
  have target := hc.targets ("natAdd_u1325", 1325) (by decide)
  natadd_step 343 using hc
  constructor
  all_goals natadd_step 344 using hc
  all_goals simpa [StatusFlags.from_result, get, even, target, Effects.All,
    BitVec.and_comm] using hp _

def tailState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem
      (get s .r10 + (get s .rdx + 2#64) * 8#64) 8 (limb + get s .r14).toInt
    regs := {s.regs with
      rdx := UInt64.ofBitVec (get s .rdx + 2#64)
      rcx := UInt64.ofBitVec (limb + get s .r14)}
    status := flags}

/-- Odd count executes the final zero-extended input read and the final word store. -/
theorem odd_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (odd : (get s .rax).extractLsb' 0 8 &&& 1#8 ≠ 0#8)
    (hl : if (get s .rdx + 2#64).toNat < (get s .r8).toNat then
      Mem.loadInt s.dmem (get s .rcx + (get s .rdx + 2#64)*8#64) 8 =
        some (limb.toNat : Int) else limb = 0)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10 + (get s .rdx + 2#64)*8#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (tailState s limb flags, base+1325)) :
    Eventually (step e) P (s, base+1297) := by
  have t1325 := hc.targets ("natAdd_u1325", 1325) (by decide)
  have t1316 := hc.targets ("natAdd_u1316", 1316) (by decide)
  by_cases present : (get s .rdx + 2#64).toNat < (get s .r8).toNat
  all_goals simp only [present, if_true, if_false] at hl
  all_goals try subst limb
  all_goals
    repeat' ((first
      | solve | simpa [tailState, get] using hp _
      | solve | simpa [get] using hm
      | apply And.intro
      | apply Delimited.store_cps
      | natadd_step 343 using hc
      | natadd_step 344 using hc
      | natadd_step 345 using hc
      | natadd_step 346 using hc
      | natadd_step 347 using hc
      | natadd_step 348 using hc
      | natadd_step 349 using hc
      | natadd_step 350 using hc
      | natadd_step 351 using hc
      | natadd_step 352 using hc) <;>
      try simp (config := {instances := true}) [StatusFlags.from_result,
        Udivti3.cf_sub, get, present, odd, t1325, t1316, Effects.All,
        BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        MachineData.load, Width.bytes, Width.bits, hl, Delimited.word_cast])

end SszX86.NatAdd.Carry.Pair
