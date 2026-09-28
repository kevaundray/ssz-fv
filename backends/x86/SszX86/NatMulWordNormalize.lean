import SszX86.NatMulWordCore

namespace SszX86.NatMulWord
open SszNative.Limbs

def normalizeState (s : MachineData) (a d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec a, r9 := UInt64.ofBitVec d}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

theorem normalize_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (normalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 48))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (normalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 73)) :
    Eventually (step e) P (normalizeState s (BitVec.ofNat 64 (n+2)) d flags, base + 48) := by
  have target := hc.targets ("natMulWord_u48", 48) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold normalizeState
  natmulword_step 0:13 using hc
  natmulword_step 0:14 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natmulword_step 0:15 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natmulword_step 0:16 using hc
  rw [scan_address]
  natmulword_load hm
  natmulword_step 0:17 using hc
  natmulword_step 0:18 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, normalizeState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, normalizeState, Effects.All] using nonzero hz _

/-- The induction bound is the original physical length, not a logical cap. -/
theorem normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ d flags,
    (∀ d flags, significantCount words n = 0 → Eventually (step e) P
      (normalizeState s 1 d flags, base + 368)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (normalizeState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 73)) →
    Eventually (step e) P (normalizeState s (BitVec.ofNat 64 (n+1)) d flags, base + 48) := by
  intro n
  induction n with
  | zero =>
    intro hn d flags zero nonzero
    have target := hc.targets ("natMulWord_u368", 368) (by decide)
    unfold normalizeState
    natmulword_step 0:13 using hc
    natmulword_step 0:14 using hc
    simpa [StatusFlags.from_result, target, normalizeState, significantCount, Effects.All]
      using zero d _ rfl
  | succ n ih =>
    intro hn d flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply normalize_step e base hc s d _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro d flags empty
        apply zero d flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

def pairState (s : MachineData) (a p d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rsi := UInt64.ofBitVec p
      r9 := UInt64.ofBitVec d}
    status := flags}

theorem normalize_publish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a : BitVec 64) (limbs : List (BitVec 64)) (flags : StatusFlags)
    (count : Nat) (positive : 0 < count) (bound : count < 2^64)
    (hm : count = 1 → Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 =
      some ((limbs[0]?.getD 0#64).toNat : Int)) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (pairState s a (if count = 1 then 0 else s.regs.rsi.toBitVec)
        (if count = 1 then limbs[0]?.getD 0 else BitVec.ofNat 64 count) flags, base + 84)) :
    Eventually (step e) P (normalizeState s a (BitVec.ofNat 64 count) flags, base + 73) := by
  have target := hc.targets ("natMulWord_u84", 84) (by decide)
  unfold normalizeState
  natmulword_step 0:19 using hc
  natmulword_step 0:20 using hc
  by_cases one : count = 1
  · have oneWord : BitVec.ofNat 64 count = 1#64 := by simp [one]
    simp [StatusFlags.from_result, oneWord, Effects.All]
    natmulword_step 0:21 using hc
    natmulword_load (hm one)
    natmulword_step 0:22 using hc
    constructor <;> simpa [pairState, one] using next _
  · have notOne : BitVec.ofNat 64 count ≠ 1#64 := by bv_omega
    simpa [StatusFlags.from_result, notOne, target, pairState, one, Effects.All] using next _

theorem normalize_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (pairState s s.regs.rax.toBitVec 0 0 flags, base + 373)) :
    Eventually (step e) P (s, base + 368) := by
  natmulword_step 2:29 using hc
  constructor <;> natmulword_step 2:30 using hc
  all_goals constructor <;> simpa [pairState] using next _

end SszX86.NatMulWord
