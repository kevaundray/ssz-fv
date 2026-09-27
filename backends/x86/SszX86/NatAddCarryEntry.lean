import SszX86.NatAddCarryLoop

namespace SszX86.NatAdd.Carry
open Kraken.X64.Parser
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def lowState (s : MachineData) (low : BitVec 64) (carry : Nat)
    (small : Bool) (flags : StatusFlags) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (get s .r10) 8 low.toInt
    regs := {s.regs with
      rbx := 1
      rbp := if small then 1 else UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++ 0#8)
      r9 := UInt64.ofBitVec low
      r11 := UInt64.ofBitVec (-get s .rax)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 carry)}
    status := flags}

/-- The initial limb and scalar-loop setup, for a nonempty physical Large LHS.
The residual R15 is immaterial at the next actual indexed-load dispatch. -/
theorem large_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : BitVec 64) (small : Bool)
    (hleftPointer : get s .rsi ≠ 0) (hleftLength : get s .rdx ≠ 0)
    (hleft : Mem.loadInt s.dmem (get s .rsi) 8 = some (left.toNat : Int))
    (hsmall : (get s .rcx = 0) ↔ small = true)
    (hright : if small then right = get s .r8 else
      if get s .r8 = 0 then right = 0 else
      Mem.loadInt s.dmem (get s .rcx) 8 = some (right.toNat : Int))
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ r15 flags, Eventually (step e) P
      ({lowState s (LimbAdd.step left right 0).1 (LimbAdd.step left right 0).2 small flags with
        regs := {(lowState s (LimbAdd.step left right 0).1
          (LimbAdd.step left right 0).2 small flags).regs with r15 := r15}}, base + 1008)) :
    Eventually (step e) P (s, base + 536) := by
  have t862 := hc.targets ("natAdd_u862", 862) (by decide)
  have t879 := hc.targets ("natAdd_u879", 879) (by decide)
  have t900 := hc.targets ("natAdd_u900", 900) (by decide)
  have t914 := hc.targets ("natAdd_u914", 914) (by decide)
  have t1060 := hc.targets ("natAdd_u1060", 1060) (by decide)
  have arithmetic := two_adds left right 0 (by omega)
  have hword : left + right = (LimbAdd.step left right 0).1 := by
    simpa [BitVec.add_comm] using arithmetic.1
  have hcarry : BitVec.ofNat 64 (Udivti3.addFlags left right).cf.toNat =
      BitVec.ofNat 64 (LimbAdd.step left right 0).2 := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using arithmetic.2
  cases small
  all_goals by_cases empty : get s .r8 = 0
  all_goals simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false,
    empty] at hright hsmall
  all_goals try subst right
  all_goals
    repeat' ((first
      | solve | simpa [lowState, get, Udivti3.addFlags, StatusFlags.from_result,
          LimbAdd.step, hword, hcarry, BitVec.ofInt_toInt, BitVec.ofInt_neg,
          BitVec.add_assoc] using hp _ _
      | solve | simpa [get] using hm
      | apply And.intro
      | apply Delimited.store_cps
      | natadd_step 138 using hc
      | natadd_step 139 using hc
      | natadd_step 140 using hc
      | natadd_step 141 using hc
      | natadd_step 142 using hc
      | natadd_step 143 using hc
      | natadd_step 225 using hc
      | natadd_step 226 using hc
      | natadd_step 227 using hc
      | natadd_step 228 using hc
      | natadd_step 229 using hc
      | natadd_step 230 using hc
      | natadd_step 231 using hc
      | natadd_step 232 using hc
      | natadd_step 233 using hc
      | natadd_step 234 using hc
      | natadd_step 235 using hc
      | natadd_step 236 using hc
      | natadd_step 237 using hc
      | natadd_step 238 using hc
      | natadd_step 239 using hc
      | natadd_step 240 using hc
      | natadd_step 241 using hc
      | natadd_step 242 using hc
      | natadd_step 243 using hc
      | natadd_step 244 using hc
      | natadd_step 245 using hc
      | natadd_step 246 using hc
      | natadd_step 247 using hc
      | natadd_step 248 using hc) <;>
      try simp (config := {instances := true}) [StatusFlags.from_result,
        get, hleftPointer, hleftLength, hsmall, empty, t862, t879, t900,
        t914, t1060, Effects.All, MachineData.load, Width.bytes, Width.bits,
        hleft, hright, Delimited.word_cast, BitVec.ofInt_add, BitVec.ofInt_toInt])

end SszX86.NatAdd.Carry
