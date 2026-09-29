import SszX86.IndicesChunkCountExec

namespace SszX86.IndicesChunkCount
open SszNative UintCodec

/-- RCX retains the original borrowed pointer and R8 retains the physical
length. Only the two loop temporaries and dead flags change. -/
def scanState (s : MachineData) (count previous : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec count,
    rdx := UInt64.ofBitVec previous}, status := flags}

private theorem scan_count_ne_one (n : Nat) (bound : n + 2 < 2^64) :
    BitVec.ofNat 64 (n+2) ≠ 1#64 := by
  intro equal
  have value := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at value
  omega

private theorem scan_decrement (n : Nat) :
    BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by
  rw [show n + 2 = (n + 1) + 1 by omega, BitVec.ofNat_add, BitVec.add_assoc]
  simp

private theorem scan_address (pointer : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (pointer.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      pointer + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  change (pointer + BitVec.ofNat 64 (n+2) * BitVec.ofNat 64 8) +
      BitVec.ofInt 64 (-16) = pointer + BitVec.ofNat 64 (8*n)
  rw [← BitVec.ofNat_mul, show (n+2)*8 = 8*n+16 by omega,
    BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc]
  simp

/-- One memory-observing iteration of the actual high-zero scan. -/
theorem scan_step (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (previous limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2^64)
    (loaded : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 272))
    (nonzero : limb ≠ 0 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 293)) :
    Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+2)) previous flags, base + 272) := by
  have target := code.targets ("indices_chunk_count_u272", 272) (by decide)
  indices_count_step 61 using code
  indices_count_step 62 using code
  simp [scanState, StatusFlags.from_result, scan_count_ne_one n bound,
    NatCompare.zf_sub, Effects.All]
  indices_count_step 63 using code
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, scan_decrement]
  indices_count_step 64 using code
  rw [scan_address]
  indices_count_load loaded
  indices_count_step 65 using code
  indices_count_step 66 using code
  by_cases hz : limb = 0#64
  · simpa [scanState, StatusFlags.from_result, hz, target, Effects.All] using zero hz _
  · simpa [scanState, StatusFlags.from_result, hz, Effects.All] using nonzero hz _

/-- Termination follows the supplied finite physical list; trailing zeros and
emptyLarge are accepted. No normalization or logical-width premise is needed. -/
theorem scan_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length + 1 < 2^64)
    (loads : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ previous flags,
      (Limbs.significantCount words n = 0 → ∀ previous flags, Eventually (step e) P
        (scanState s 1 previous flags, base + 326)) →
      (0 < Limbs.significantCount words n → ∀ flags, Eventually (step e) P
        (scanState s (BitVec.ofNat 64 (Limbs.significantCount words n))
          (BitVec.ofNat 64 (Limbs.significantCount words n)) flags, base + 293)) →
      Eventually (step e) P
        (scanState s (BitVec.ofNat 64 (n+1)) previous flags, base + 272) := by
  intro n
  induction n with
  | zero =>
    intro hn previous flags zero nonzero
    have target := code.targets ("indices_chunk_count_u326", 326) (by decide)
    indices_count_step 61 using code
    indices_count_step 62 using code
    simpa [scanState, StatusFlags.from_result, target, Effects.All] using zero rfl previous _
  | succ n ih =>
    intro hn previous flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using loads ⟨n, by omega⟩
    apply scan_step e base code s previous _ flags n (by omega) loaded P
    · intro hz fl
      apply ih (by omega) _ fl
      · simpa [Limbs.significantCount, hz] using zero
      · simpa [Limbs.significantCount, hz] using nonzero
    · intro hz fl
      simpa [Limbs.significantCount, hz] using
        nonzero (by simp [Limbs.significantCount, hz]) fl

end SszX86.IndicesChunkCount
