import SszX86.NatDivisionCore

namespace SszX86.NatDivision
open SszNative.Limbs
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def scanState (s : MachineData) (a c : BitVec 64) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with rax := UInt64.ofBitVec a, rcx := UInt64.ofBitVec c }
    status := flags }

@[simp] theorem scanState_initial (s : MachineData) :
    scanState s s.regs.rax.toBitVec s.regs.rcx.toBitVec s.status = s := by
  cases s with | mk regs zmms status dmem => cases regs <;> rfl

/-- One original-representation scan iteration. No input limb is modified. -/
theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (hz : limb = 0#64 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 48))
    (hn : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 73)) :
    Eventually (step e) P (scanState s (BitVec.ofNat 64 (n+2)) c flags, base + 48) := by
  have target := hc.targets ("natDivision_u48", 48) (by decide)
  have hne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hdec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have haddr : BitVec.ofInt 64 (s.regs.rsi.toBitVec.toInt +
      (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  simp only [scanState]
  natdiv_step 15 using hc
  natdiv_step 16 using hc
  simp [StatusFlags.from_result, hne, Effects.All]
  natdiv_step 17 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hdec]
  natdiv_step 18 using hc
  rw [haddr]
  natdiv_load hm
  natdiv_step 19 using hc
  natdiv_step 20 using hc
  by_cases hl : limb = 0#64
  · simpa [StatusFlags.from_result, hl, target, scanState, Effects.All] using hz hl _
  · simpa [StatusFlags.from_result, hl, scanState, Effects.All] using hn hl _

/-- Complete high-zero scan at PC48. The nonzero exit carries the exact
significant count; all-zero input exits to the real zero/small dispatch. -/
theorem scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ c flags,
    (significantCount words n = 0 → ∀ c flags, Eventually (step e) P
      (scanState s 1#64 c flags, base + 221)) →
    (0 < significantCount words n → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 73)) →
    Eventually (step e) P (scanState s (BitVec.ofNat 64 (n+1)) c flags, base + 48) := by
  intro n
  induction n with
  | zero =>
    intro hn c flags hz hp
    have target := hc.targets ("natDivision_u221", 221) (by decide)
    simp only [scanState]
    natdiv_step 15 using hc
    natdiv_step 16 using hc
    simpa [StatusFlags.from_result, target, Effects.All, scanState] using
      hz (by simp [significantCount]) c _
  | succ n ih =>
    intro hn c flags hz hp
    have hload : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply scan_step e base hc s c _ flags n (by omega) hload P
    · intro hl fl
      apply ih (by omega) _ fl
      · intro hs c fl
        apply hz (by simpa [significantCount, hl] using hs)
      · intro hs fl
        simpa [significantCount, hl] using hp (by simpa [significantCount, hl] using hs) fl
    · intro hl fl
      simpa [significantCount, hl] using hp (by simp [significantCount, hl]) fl

end SszX86.NatDivision
