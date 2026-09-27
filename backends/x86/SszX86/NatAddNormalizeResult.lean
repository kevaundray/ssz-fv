import SszX86.NatAddNormalizeLeft

namespace SszX86.NatAdd
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

/-- The final scan reads the entire allocated buffer, including the final carry
slot even when zero; it never shortens the recorded allocation or written list. -/
theorem result_normalize_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.r10.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (leftNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 1344))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (leftNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 1365)) :
    Eventually (step e) P (leftNormalizeState s (BitVec.ofNat 64 (n+2)) d flags, base + 1344) := by
  have target := hc.targets ("natAdd_u1344", 1344) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold leftNormalizeState
  natadd_step 357 using hc
  natadd_step 358 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natadd_step 359 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natadd_step 360 using hc
  rw [scan_address]
  natadd_load hm
  natadd_step 361 using hc
  natadd_step 362 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, leftNormalizeState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, leftNormalizeState, Effects.All] using nonzero hz _

theorem result_normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r10.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ d flags,
    (∀ d flags, significantCount words n = 0 → Eventually (step e) P
      (leftNormalizeState s 1 d flags, base + 1384)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (leftNormalizeState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 1365)) →
    Eventually (step e) P (leftNormalizeState s (BitVec.ofNat 64 (n+1)) d flags, base + 1344) := by
  intro n
  induction n with
  | zero =>
    intro hn d flags zero nonzero
    have target := hc.targets ("natAdd_u1384", 1384) (by decide)
    unfold leftNormalizeState
    natadd_step 357 using hc
    natadd_step 358 using hc
    simpa [StatusFlags.from_result, target, leftNormalizeState, significantCount, Effects.All]
      using zero d _ rfl
  | succ n ih =>
    intro hn d flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.r10.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply result_normalize_step e base hc s d _ flags n (by omega) loaded P
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

def resultPairState (s : MachineData) (count : BitVec 64) (flags : StatusFlags) : MachineData :=
  let payload := if count = 1#64 then s.regs.r9.toBitVec else count
  {s with
    regs := {s.regs with
      rax := 0
      rdx := UInt64.ofBitVec count
      rcx := UInt64.ofBitVec payload
      r9 := UInt64.ofBitVec payload
      r10 := if count = 1#64 then 0 else s.regs.r10}
    status := flags}

theorem result_normalize_publish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a count : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (resultPairState s count flags, base + 1387)) :
    Eventually (step e) P (leftNormalizeState s a count flags, base + 1365) := by
  unfold leftNormalizeState
  natadd_step 363 using hc
  constructor <;> natadd_step 364 using hc
  all_goals natadd_step 365 using hc
  all_goals natadd_step 366 using hc
  all_goals natadd_step 367 using hc
  all_goals natadd_step 368 using hc
  all_goals
    by_cases one : count = 1#64
    · simpa [StatusFlags.from_result, one, resultPairState] using next _
    · simpa [StatusFlags.from_result, one, resultPairState] using next _

theorem result_normalize_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r10 := 0}, status := flags}, base + 1387)) :
    Eventually (step e) P (s, base + 1384) := by
  natadd_step 369 using hc
  constructor <;> exact next _

end SszX86.NatAdd
