import SszX86.NatAddCarryPairBridges

namespace SszX86.NatAdd.Carry.Pair
open Kraken.X64.Parser
open UintCodec
open UintCodec.Large

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem second_loaded_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (first second : BitVec 64) (loadFlags : StatusFlags)
    (hmsecond : ∃ old,
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (secondAddress s) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (pairState s first second flags,
      if get s .rsi + 1#64 = get s .r11 then base + 1297 else base + 1252)) :
    Eventually (step e) P (secondLoadedState s first second loadFlags, base + 1226) := by
  apply Cuts.second_add_cps e base hc (secondLoadedState s first second loadFlags)
    (firstCarry s first) (second_loaded_si s first second loadFlags)
    (second_loaded_bpl s first second loadFlags) P
  intro addFlags
  rw [second_add_bridge]
  apply Cuts.second_store_cps e base hc (secondAddedState s first second addFlags)
  · exact hmsecond
  rw [second_store_bridge]
  apply Cuts.finish_cps e base hc (secondStoredState s first second addFlags) P
  intro finishFlags
  rw [finish_bridge]
  change Eventually (step e) P (pairState s first second finishFlags,
    if get s .rsi + 1#64 = get s .r11 then base + 1297 else base + 1252)
  exact hp finishFlags

private theorem first_stored_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (first second : BitVec 64) (storeFlags : StatusFlags)
    (hsecond : if (get s .rsi + 1#64).toNat < (get s .r8).toNat then
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (get s .rcx + get s .rsi * 8#64 + 8#64) 8 = some (second.toNat : Int)
      else second = 0)
    (hmsecond : ∃ old,
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (secondAddress s) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (pairState s first second flags,
      if get s .rsi + 1#64 = get s .r11 then base + 1297 else base + 1252)) :
    Eventually (step e) P (firstStoredState s first storeFlags, base + 1283) := by
  apply Cuts.second_guard_cps e base hc (firstStoredState s first storeFlags) P
  intro guardFlags
  rw [second_guard_bridge]
  change Eventually (step e) P (secondReadyState s first guardFlags,
    if (get s .rsi + 1#64).toNat < (get s .r8).toNat then base + 1221 else base + 1292)
  by_cases present : (get s .rsi + 1#64).toNat < (get s .r8).toNat
  · simp only [present, ↓reduceIte]
    apply Cuts.load_second_cps e base hc (secondReadyState s first guardFlags) second
    · simpa only [present, ↓reduceIte] using hsecond
    rw [second_load_bridge]
    exact second_loaded_cps e base hc s first second guardFlags hmsecond P hp
  · have zero : second = 0 := by simpa only [present, ↓reduceIte] using hsecond
    simp only [present, ↓reduceIte]
    apply Cuts.zero_second_cps e base hc (secondReadyState s first guardFlags) P
    intro zeroFlags
    rw [second_load_bridge]
    simpa only [zero] using second_loaded_cps e base hc s first second zeroFlags hmsecond P hp

private theorem first_loaded_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (first second : BitVec 64) (startFlags loadFlags : StatusFlags)
    (hsecond : if (get s .rsi + 1#64).toNat < (get s .r8).toNat then
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (get s .rcx + get s .rsi * 8#64 + 8#64) 8 = some (second.toNat : Int)
      else second = 0)
    (hmfirst : ∃ old, Mem.loadInt s.dmem (firstAddress s) 8 = some old)
    (hmsecond : ∃ old,
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (secondAddress s) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (pairState s first second flags,
      if get s .rsi + 1#64 = get s .r11 then base + 1297 else base + 1252)) :
    Eventually (step e) P
      (Cuts.firstLoadState (Cuts.startState s startFlags) first loadFlags, base + 1269) := by
  apply Cuts.first_add_cps e base hc _ P
  intro addFlags
  rw [first_add_bridge]
  apply Cuts.first_store_cps e base hc (firstState s first addFlags)
  · exact hmfirst
  rw [first_store_bridge]
  exact first_stored_cps e base hc s first second addFlags hsecond hmsecond P hp

/-- The actual paired-unrolled loop body writes two consecutive limbs before
its comparison with the even part of the significant count. -/
theorem pair_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (first second : BitVec 64)
    (hfirst : if (get s .rsi).toNat < (get s .r8).toNat then
      Mem.loadInt s.dmem (get s .rcx + get s .rsi * 8#64) 8 = some (first.toNat : Int)
      else first = 0)
    (hsecond : if (get s .rsi + 1#64).toNat < (get s .r8).toNat then
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (get s .rcx + get s .rsi * 8#64 + 8#64) 8 = some (second.toNat : Int)
      else second = 0)
    (hmfirst : ∃ old, Mem.loadInt s.dmem (firstAddress s) 8 = some old)
    (hmsecond : ∃ old,
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
        (secondAddress s) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (pairState s first second flags,
        if get s .rsi + 1#64 = get s .r11 then base + 1297 else base + 1252)) :
    Eventually (step e) P (s, base + 1252) := by
  apply Cuts.start_cps e base hc s P
  intro startFlags
  change Eventually (step e) P (Cuts.startState s startFlags,
    if (get s .rsi).toNat < (get s .r8).toNat then base + 1260 else base + 1266)
  by_cases present : (get s .rsi).toNat < (get s .r8).toNat
  · simp only [present, ↓reduceIte]
    apply Cuts.load_first_cps e base hc (Cuts.startState s startFlags) first
    · simpa only [present, ↓reduceIte] using hfirst
    exact first_loaded_cps e base hc s first second startFlags startFlags
      hsecond hmfirst hmsecond P hp
  · have zero : first = 0 := by simpa only [present, ↓reduceIte] using hfirst
    simp only [present, ↓reduceIte]
    apply Cuts.zero_first_cps e base hc (Cuts.startState s startFlags) P
    intro zeroFlags
    simpa only [zero] using first_loaded_cps e base hc s first second startFlags zeroFlags
      hsecond hmfirst hmsecond P hp

end SszX86.NatAdd.Carry.Pair
