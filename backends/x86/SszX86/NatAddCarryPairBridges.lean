import SszX86.NatAddCarryPairState
import SszX86.NatAddCarryPairLoads
import SszX86.NatAddCarryPairArithmetic
import SszX86.NatAddCarryPairStores

namespace SszX86.NatAdd.Carry.Pair

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem first_add_bridge (s : MachineData) (first : BitVec 64)
    (startFlags loadFlags addFlags : StatusFlags) :
    Cuts.firstAddState (Cuts.firstLoadState (Cuts.startState s startFlags) first loadFlags) addFlags =
      firstState s first addFlags := by
  simp only [Cuts.firstAddState, Cuts.firstLoadState, Cuts.startState, firstState,
    firstWord, firstCarry, get, SszX86.NatAdd.Carry.get, Reg64s.get64,
    UInt64.toBitVec_ofBitVec, Udivti3.addFlags_cf, UInt64.toNat_toBitVec,
    BitVec.add_comm, Nat.add_comm]

theorem first_store_bridge (s : MachineData) (first : BitVec 64) (flags : StatusFlags) :
    Cuts.firstStoreState (firstState s first flags) = firstStoredState s first flags := by
  rfl

theorem second_guard_bridge (s : MachineData) (first : BitVec 64)
    (oldFlags flags : StatusFlags) :
    Cuts.secondGuardState (firstStoredState s first oldFlags) flags =
      secondReadyState s first flags := by
  rfl

theorem second_load_bridge (s : MachineData) (first second : BitVec 64)
    (oldFlags flags : StatusFlags) :
    Cuts.secondLoadState (secondReadyState s first oldFlags) second flags =
      secondLoadedState s first second flags := by
  rfl

theorem second_loaded_si (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) :
    (secondLoadedState s first second flags).regs.rsi = 0 := by
  rfl

theorem second_loaded_bpl (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) :
    (SszX86.NatAdd.Carry.get (secondLoadedState s first second flags) .rbp).setWidth 8 =
      BitVec.ofNat 8 (firstCarry s first).toNat := by
  exact BitVec.setWidth_append_eq_right

theorem second_add_bridge (s : MachineData) (first second : BitVec 64)
    (oldFlags flags : StatusFlags) :
    Cuts.secondAddState (secondLoadedState s first second oldFlags) (firstCarry s first) flags =
      secondAddedState s first second flags := by
  simp only [Cuts.secondAddState, secondAddedState, secondLoadedState, secondReadyState,
    firstStoredState, firstState, secondWord, secondCarry, get, SszX86.NatAdd.Carry.get,
    Reg64s.get64, UInt64.toBitVec_ofBitVec, Udivti3.addFlags_cf,
    BitVec.add_comm, Nat.add_comm]

theorem second_store_bridge (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) :
    Cuts.secondStoreState (secondAddedState s first second flags) =
      secondStoredState s first second flags := by
  rfl

theorem finish_bridge (s : MachineData) (first second : BitVec 64)
    (oldFlags flags : StatusFlags) :
    Cuts.finishState (secondStoredState s first second oldFlags) flags =
      pairState s first second flags := by
  simp only [Cuts.finishState, secondStoredState, secondAddedState, secondLoadedState,
    secondReadyState, firstStoredState, firstState, pairState, get, SszX86.NatAdd.Carry.get,
    Reg64s.get64, UInt64.toBitVec_ofBitVec, BitVec.add_assoc,
    show 1#64 + 1#64 = 2#64 by decide]

end SszX86.NatAdd.Carry.Pair
