import SszX86.NatAddCarrySmallEntryCuts
import SszX86.NatAddCarryEntryLoads
import SszX86.NatAddCarryEntryStores

namespace SszX86.NatAdd.Carry.Pair
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def headState (s : MachineData) (right : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem (get s .r10) 8 (get s .rdx + right).toInt
    regs := {s.regs with
      rsi := 1
      rbx := UInt64.ofBitVec (get s .rbx + 8#64)
      rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++ 1#8)
      r9 := UInt64.ofBitVec (get s .rdx + right)
      r11 := UInt64.ofBitVec (get s .r11 &&& get s .rax)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 (Udivti3.addFlags (get s .rdx) right).cf.toNat)
      r15 := UInt64.ofBitVec right}
    status := flags}

private def headLoadedState (s : MachineData) (right : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r9 := s.regs.rdx, r14 := 0, r15 := UInt64.ofBitVec right}
    status := flags}

private def headStoredState (s : MachineData) (right : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem (get s .r10) 8 (right + get s .rdx).toInt
    regs := {s.regs with
      r9 := UInt64.ofBitVec (right + get s .rdx)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 (Udivti3.addFlags right (get s .rdx)).cf.toNat)
      r15 := UInt64.ofBitVec right}
    status := flags}

private theorem head_loaded_eq (s : MachineData) (right : BitVec 64)
    (seedFlags readFlags : StatusFlags) :
    Entry.rightState (SmallEntry.seedState s seedFlags) right readFlags =
      headLoadedState s right readFlags := by
  rfl

private theorem head_stored_eq (s : MachineData) (right : BitVec 64)
    (readFlags addFlags : StatusFlags) :
    Entry.sumStoredState (headLoadedState s right readFlags) right addFlags =
      headStoredState s right addFlags := by
  rfl

private theorem head_state_eq (s : MachineData) (right : BitVec 64)
    (addFlags markFlags countFlags setupFlags : StatusFlags) :
    SmallEntry.setupState
      {Entry.largeMarkedState (headStoredState s right addFlags) markFlags with status := countFlags}
      setupFlags = headState s right setupFlags := by
  simp [SmallEntry.setupState, Entry.largeMarkedState, headStoredState, headState,
    get, Reg64s.get64, Udivti3.addFlags_cf, BitVec.add_comm, UInt64.add_comm, Nat.add_comm]

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
  have finishStored (addFlags : StatusFlags) :
      Eventually (step e) P (headStoredState s right addFlags, base + 927) := by
    apply Entry.large_mark_cps e base hc
    intro markFlags
    have zero : get (headStoredState s right addFlags) .rsi = 0 := hleft
    rw [ite_eq_left zero]
    apply SmallEntry.count_cps e base hc
    · exact hcount
    intro countFlags
    apply SmallEntry.setup_cps e base hc
    intro setupFlags
    rw [head_state_eq]
    exact hp setupFlags
  have finishLoaded (readFlags : StatusFlags) :
      Eventually (step e) P (headLoadedState s right readFlags, base + 917) := by
    apply Entry.large_sum_store_cps e base hc
    · rfl
    · exact hm
    intro addFlags
    change Eventually (step e) P
      (Entry.sumStoredState (headLoadedState s right readFlags) right addFlags, base + 927)
    rw [head_stored_eq]
    exact finishStored addFlags
  apply SmallEntry.left_cps e base hc s hleft P
  intro leftFlags
  apply SmallEntry.pointer_cps e base hc
  · exact hpointer
  intro pointerFlags
  apply SmallEntry.seed_cps e base hc
  intro seedFlags
  change Eventually (step e) P (SmallEntry.seedState s seedFlags, base + 890)
  apply SmallEntry.length_cps e base hc
  · exact hlength
  intro lengthFlags
  change Eventually (step e) P (SmallEntry.seedState s lengthFlags, base + 895)
  apply Entry.right_cps e base hc _ right
  · exact hright
  rw [head_loaded_eq]
  exact finishLoaded lengthFlags

end SszX86.NatAdd.Carry.Pair
