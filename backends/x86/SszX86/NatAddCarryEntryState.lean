import SszX86.NatAddCarryEntryLoads
import SszX86.NatAddCarryEntryStores
import SszX86.NatAddCarryEntrySetup

namespace SszX86.NatAdd.Carry
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def lowState (s : MachineData) (low : BitVec 64) (carry : Nat)
    (small : Bool) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem (get s .r10) 8 low.toInt
    regs := {s.regs with
      rbx := 1
      rbp := if small then 1 else UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++ 0#8)
      r9 := UInt64.ofBitVec low
      r11 := UInt64.ofBitVec (-get s .rax)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 carry)}
    status := flags}

namespace Entry

private theorem high_byte_append (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 8 56 = hi := by
  exact BitVec.extractLsb'_append_eq_left

private theorem low_byte_append (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).setWidth 8 = lo := BitVec.setWidth_append_eq_right

theorem small_finish_bridge (s : MachineData) (left right : BitVec 64)
    (leftFlags clearFlags addFlags markFlags flags : StatusFlags) :
    setupState (smallMarkedState
      (sumStoredState (clearedState (leftState s left leftFlags) clearFlags) right addFlags)
      markFlags) flags =
      {lowState s (LimbAdd.step left right 0).1 (LimbAdd.step left right 0).2 true flags with
        regs := {(lowState s (LimbAdd.step left right 0).1 (LimbAdd.step left right 0).2 true flags).regs with
          r15 := s.regs.r15}} := by
  have arithmetic := initial_add left right
  simp only [setupState, smallMarkedState, sumStoredState, addedState, clearedState,
    leftState, lowState, get, Reg64s.get64, UInt64.toBitVec_ofBitVec,
    arithmetic.1, arithmetic.2]
  all_goals rfl

theorem large_finish_bridge (s : MachineData) (left right : BitVec 64)
    (leftFlags clearFlags loadFlags addFlags markFlags flags : StatusFlags) :
    setupState (largeMarkedState
      (sumStoredState (rightState (clearedState (leftState s left leftFlags) clearFlags) right loadFlags)
        right addFlags) markFlags) flags =
      {lowState s (LimbAdd.step left right 0).1 (LimbAdd.step left right 0).2 false flags with
        regs := {(lowState s (LimbAdd.step left right 0).1 (LimbAdd.step left right 0).2 false flags).regs with
          r15 := UInt64.ofBitVec right}} := by
  have arithmetic := initial_add left right
  simp only [setupState, largeMarkedState, sumStoredState, addedState, rightState,
    clearedState, leftState, lowState, get, Reg64s.get64, UInt64.toBitVec_ofBitVec,
    high_byte_append, low_byte_append, show 1#8 ^^^ 1#8 = 0#8 by decide,
    arithmetic.1, arithmetic.2]
  all_goals rfl

end Entry
end SszX86.NatAdd.Carry
