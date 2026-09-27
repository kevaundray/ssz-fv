import SszX86.NatDivisionCore

namespace SszX86.NatDivision
open SszNative.Limbs
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def countState (s : MachineData) (a bp skipped saved : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with
      rax := UInt64.ofBitVec a, rbp := UInt64.ofBitVec bp
      r8 := UInt64.ofBitVec skipped, r13 := UInt64.ofBitVec saved }
    status := flags }

/-- The allocator's rescan also computes the reverse-loop byte index and the
number of redundant high words. It still reads the original borrowed limbs. -/
theorem count_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (bp skipped saved limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (hz : limb = 0#64 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+1)) (bp+8) (skipped+1)
        (BitVec.ofNat 64 (n+2)) flags, base + 128))
    (hn : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+1)) (bp+8) (skipped+1)
        (BitVec.ofNat 64 (n+2)) flags, base + 160)) :
    Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+2)) bp skipped saved flags, base + 128) := by
  have target := hc.targets ("natDivision_u128", 128) (by decide)
  have hne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hdec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have haddr : BitVec.ofInt 64 (s.regs.rsi.toBitVec.toInt +
      (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  simp only [countState]
  natdiv_step 32 using hc
  natdiv_step 33 using hc
  natdiv_step 34 using hc
  simp [StatusFlags.from_result, hne, Effects.All]
  natdiv_step 35 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hdec]
  natdiv_step 36 using hc
  natdiv_step 37 using hc
  natdiv_step 38 using hc
  rw [haddr]
  natdiv_load hm
  natdiv_step 39 using hc
  by_cases hl : limb = 0#64
  · simpa [StatusFlags.from_result, hl, target, countState, Effects.All, UInt64.add_comm] using hz hl _
  · simpa [StatusFlags.from_result, hl, countState, Effects.All, UInt64.add_comm] using hn hl _

/-- Positive significant count rules out the compiler's dormant all-zero
rescan exit; this follows from the caller's preceding original-operand scan. -/
theorem count_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → 0 < significantCount words n → ∀ bp skipped saved flags,
    (∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (significantCount words n))
        (bp + BitVec.ofNat 64 (8*(n-significantCount words n+1)))
        (skipped + BitVec.ofNat 64 (n-significantCount words n+1))
        (BitVec.ofNat 64 (significantCount words n+1)) flags, base + 160)) →
    Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+1)) bp skipped saved flags, base + 128) := by
  intro n
  induction n with
  | zero => intro _ impossible; simp [significantCount] at impossible
  | succ n ih =>
    intro hn positive bp skipped saved flags hp
    have hload : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply count_step e base hc s bp skipped saved _ flags n (by omega) hload P
    · intro hl fl
      have pos : 0 < significantCount words n := by
        simpa [significantCount, hl] using positive
      apply ih (by omega) pos (bp+8) (skipped+1) _ fl
      intro fl
      have hk : significantCount words n ≤ n := significantCount_le words n
      have distance : n+1-significantCount words n+1 = (n-significantCount words n+1)+1 := by omega
      have left_comm (a b c : BitVec 64) : a + (b+c) = b + (a+c) := by
        rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]
      simpa [significantCount, hl, distance, Nat.mul_add, BitVec.ofNat_add,
        BitVec.add_assoc, left_comm, BitVec.add_comm] using hp fl
    · intro hl fl
      simpa [significantCount, hl] using hp fl

end SszX86.NatDivision
