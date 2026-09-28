import SszX86.NatAddCarryFetchLoads
import SszX86.NatAddCarryFetchSelect

namespace SszX86.NatAdd.Carry
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def fetchState (s : MachineData) (left right : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r12 := UInt64.ofBitVec right
      r15 := UInt64.ofBitVec left}
    status := flags}

private theorem fetch_right_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (right : BitVec 64) (small mirror : Bool)
    (hbpl : (get s .rbp).extractLsb' 0 8 = if small then 1#8 else 0#8)
    (hr : if ¬small ∧ (get s .rbx).toNat < (get s .r8).toNat then
      Mem.loadInt s.dmem (get s .rcx + get s .rbx * 8#64) 8 = some (right.toNat : Int)
      else right = 0)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (Fetch.rightState s right flags, base + 964)) :
    Eventually (step e) P (s, if mirror then base + 1043 else base + 1017) := by
  apply Fetch.select_cps e base hc s small mirror hbpl P
  intro scratch flags hzf
  apply Fetch.right_branch_cps e base hc (Fetch.selectState s scratch flags) mirror P
  change Eventually (step e) P (Fetch.selectState s scratch flags,
    if flags.zf then base + 960 else if mirror then base + 1055 else base + 1029)
  rw [hzf]
  by_cases present : ¬small ∧ (get s .rbx).toNat < (get s .r8).toNat
  · simp only [Fetch.selectFlag, present]
    apply Fetch.load_right_cps e base hc (Fetch.selectState s scratch flags) right
    · rw [ite_eq_left present] at hr
      simpa only [Fetch.selectState, get, Reg64s.get64] using hr
    · simpa only [Fetch.rightState, Fetch.selectState] using hp flags
  · have zero : right = 0 := by simpa only [present, ↓reduceIte] using hr
    have skipped : Eventually (step e) P (Fetch.selectState s scratch flags, base + 1055) := by
      apply Fetch.zero_right_cps e base hc (Fetch.selectState s scratch flags) P
      intro finalFlags
      simpa only [Fetch.rightState, Fetch.selectState, zero] using hp finalFlags
    simp only [Fetch.selectFlag, present]
    cases mirror with
    | false => exact Fetch.skip_right_cps e base hc _ P skipped
    | true => exact skipped

/-- Original unsigned physical lengths select both indexed loads. A small RHS
is zero beyond limb zero, regardless of its arbitrary word-valued payload. -/
theorem fetch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : BitVec 64) (small : Bool)
    (hbpl : (get s .rbp).extractLsb' 0 8 = if small then 1#8 else 0#8)
    (hl : if (get s .rbx).toNat < (get s .rdx).toNat then
      Mem.loadInt s.dmem (get s .rsi + get s .rbx * 8#64) 8 = some (left.toNat : Int)
      else left = 0)
    (hr : if ¬small ∧ (get s .rbx).toNat < (get s .r8).toNat then
      Mem.loadInt s.dmem (get s .rcx + get s .rbx * 8#64) 8 = some (right.toNat : Int)
      else right = 0)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (fetchState s left right flags, base + 964)) :
    Eventually (step e) P (s, base + 1008) := by
  apply Fetch.left_branch_cps e base hc s P
  intro flags
  by_cases present : (get s .rbx).toNat < (get s .rdx).toNat
  · simp only [present, ↓reduceIte]
    apply Fetch.load_left_cps e base hc {s with status := flags} left
    · simpa only [present, ↓reduceIte] using hl
    change Eventually (step e) P (Fetch.leftState s left flags, base + 1017)
    apply fetch_right_cps e base hc (Fetch.leftState s left flags) right small false
    · exact hbpl
    · exact hr
    · intro finalFlags
      simpa only [Fetch.rightState, Fetch.leftState, fetchState] using hp finalFlags
  · have zero : left = 0 := by simpa only [present, ↓reduceIte] using hl
    simp only [present, ↓reduceIte]
    apply Fetch.zero_left_cps e base hc {s with status := flags} P
    intro zeroFlags
    change Eventually (step e) P (Fetch.leftState s 0 zeroFlags, base + 1043)
    apply fetch_right_cps e base hc (Fetch.leftState s 0 zeroFlags) right small true
    · exact hbpl
    · exact hr
    · intro finalFlags
      simpa only [Fetch.rightState, Fetch.leftState, fetchState, zero] using hp finalFlags

end SszX86.NatAdd.Carry
