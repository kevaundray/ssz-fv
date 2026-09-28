import SszX86.NatAddCarryLoop
import SszX86.NatAddCarryEntryState

namespace SszX86.NatAdd.Carry
open Kraken.X64.Parser
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem large_rhs_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : BitVec 64)
    (leftFlags clearFlags loadFlags : StatusFlags)
    (hleftPointer : get s .rsi ≠ 0)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ r15 flags, Eventually (step e) P
      ({lowState s (LimbAdd.step left right 0).1 (LimbAdd.step left right 0).2 false flags with
        regs := {(lowState s (LimbAdd.step left right 0).1
          (LimbAdd.step left right 0).2 false flags).regs with r15 := r15}}, base + 1008)) :
    Eventually (step e) P
      (Entry.rightState (Entry.clearedState (Entry.leftState s left leftFlags) clearFlags)
        right loadFlags, base + 917) := by
  apply Entry.large_sum_store_cps e base hc _ (by rfl)
  · exact hm
  intro addFlags
  change Eventually (step e) P
    (Entry.sumStoredState
      (Entry.rightState (Entry.clearedState (Entry.leftState s left leftFlags) clearFlags)
        right loadFlags) right addFlags, base + 927)
  apply Entry.large_mark_cps e base hc _ P
  intro markFlags
  change Eventually (step e) P
    (Entry.largeMarkedState
      (Entry.sumStoredState
        (Entry.rightState (Entry.clearedState (Entry.leftState s left leftFlags) clearFlags)
          right loadFlags) right addFlags) markFlags,
      if get s .rsi = 0 then base + 1060 else base + 935)
  simp only [hleftPointer, ↓reduceIte]
  apply Entry.setup_cps e base hc _ P
  intro flags
  rw [Entry.large_finish_bridge]
  exact hp (UInt64.ofBitVec right) flags

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
  apply Entry.left_cps e base hc s left hleftPointer hleftLength hleft P
  intro leftFlags
  apply Entry.dispatch_cps e base hc (Entry.leftState s left leftFlags) P
  intro clearFlags
  change Eventually (step e) P
    (Entry.clearedState (Entry.leftState s left leftFlags) clearFlags,
      if get s .rcx = 0 then base + 900 else if get s .r8 = 0 then base + 914 else base + 895)
  cases small with
  | true =>
    have pointerZero : get s .rcx = 0 := hsmall.mpr rfl
    have rightWord : right = get s .r8 := by simpa only [↓reduceIte] using hright
    simp only [pointerZero, ↓reduceIte]
    apply Entry.small_add_cps e base hc _ (by rfl) P
    intro addFlags
    change Eventually (step e) P
      (Entry.addedState (Entry.clearedState (Entry.leftState s left leftFlags) clearFlags)
        (get s .r8) addFlags, base + 907)
    rw [← rightWord]
    apply Entry.small_store_cps e base hc _
    · exact hm
    change Eventually (step e) P
      (Entry.sumStoredState (Entry.clearedState (Entry.leftState s left leftFlags) clearFlags)
        right addFlags, base + 910)
    apply Entry.small_mark_cps e base hc _ P
    intro markFlags
    apply Entry.setup_cps e base hc _ P
    intro flags
    rw [Entry.small_finish_bridge]
    exact hp s.regs.r15 flags
  | false =>
    have pointerNonzero : get s .rcx ≠ 0 := by
      intro zero
      have bad : false = true := hsmall.mp zero
      cases bad
    simp only [pointerNonzero, ↓reduceIte]
    by_cases empty : get s .r8 = 0
    · have zeroRight : right = 0 := by simpa only [Bool.false_eq_true, empty, ↓reduceIte] using hright
      simp only [empty, ↓reduceIte]
      apply Entry.zero_right_cps e base hc _ P
      intro loadFlags
      simpa only [zeroRight] using large_rhs_cps e base hc s left right
        leftFlags clearFlags loadFlags hleftPointer hm P hp
    · have loaded : Mem.loadInt s.dmem (get s .rcx) 8 = some (right.toNat : Int) := by
        simpa only [Bool.false_eq_true, empty, ↓reduceIte] using hright
      simp only [empty, ↓reduceIte]
      apply Entry.right_cps e base hc _ right
      · simpa only [Entry.clearedState, Entry.leftState, get, Reg64s.get64] using loaded
      · exact large_rhs_cps e base hc s left right leftFlags clearFlags clearFlags
          hleftPointer hm P hp

end SszX86.NatAdd.Carry
