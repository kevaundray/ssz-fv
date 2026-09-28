import SszX86.NatAddCarryTailCuts

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
  apply Tail.parity_cps e base hc s P
  intro flags
  rw [ite_eq_left even]
  exact hp flags

def tailState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem
      (get s .r10 + (get s .rdx + 2#64) * 8#64) 8 (limb + get s .r14).toInt
    regs := {s.regs with
      rdx := UInt64.ofBitVec (get s .rdx + 2#64)
      rcx := UInt64.ofBitVec (limb + get s .r14)}
    status := flags}

private theorem tail_state_eq (s : MachineData) (limb : BitVec 64)
    (indexFlags wordFlags sumFlags : StatusFlags) :
    Tail.storedState
      (Tail.sumState (Tail.wordState (Tail.indexState s indexFlags) limb wordFlags) sumFlags) =
      tailState s limb sumFlags := by
  rfl

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
  have finish (indexFlags wordFlags : StatusFlags) :
      Eventually (step e) P
        (Tail.wordState (Tail.indexState s indexFlags) limb wordFlags, base + 1318) := by
    apply Tail.sum_cps e base hc
    intro sumFlags
    apply Tail.store_cps e base hc
    · simpa only [Tail.address, Tail.sumState, Tail.wordState, Tail.indexState,
        get, Reg64s.get64, UInt64.toBitVec_ofBitVec] using hm
    · rw [tail_state_eq]
      exact hp sumFlags
  apply Tail.parity_cps e base hc s P
  intro parityFlags
  rw [ite_eq_right odd]
  apply Tail.index_cps e base hc
  intro indexFlags
  change Eventually (step e) P (Tail.indexState s indexFlags,
    if (get s .rdx + 2#64).toNat < (get s .r8).toNat then base + 1310 else base + 1316)
  by_cases present : (get s .rdx + 2#64).toNat < (get s .r8).toNat
  · rw [ite_eq_left present]
    rw [ite_eq_left present] at hl
    apply Tail.word_cps e base hc _ limb
    · simpa only [Tail.indexState, get, Reg64s.get64, UInt64.toBitVec_ofBitVec] using hl
    · exact finish indexFlags indexFlags
  · rw [ite_eq_right present]
    rw [ite_eq_right present] at hl
    subst limb
    apply Tail.zero_cps e base hc
    intro wordFlags
    exact finish indexFlags wordFlags

end SszX86.NatAdd.Carry.Pair
