import SszX86.NatDivisionCopyInit

namespace SszX86.NatDivision.Copy
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- State at PC669. The memory index is also the number of completed writes. -/
def loopState (s : MachineData) (destination : BitVec 64) (words : List (BitVec 64))
    (i : Nat) (previous last : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec (BitVec.ofNat 64 i)
      r8 := UInt64.ofBitVec previous
      r11 := UInt64.ofBitVec last}
    dmem := memory s.dmem destination words i
    status := flags}

private theorem first_address (s : MachineData) (destination : BitVec 64)
    (words : List (BitVec 64)) (i : Nat) (previous last : BitVec 64) (flags : StatusFlags)
    (pointer : get s .r9 = destination + 8#64) :
    firstAddress (loopState s destination words i previous last flags) =
      destination + BitVec.ofNat 64 (8*i) := by
  simp only [firstAddress, loopState, get, Reg64s.get64] at *
  rw [pointer]
  bv_omega

private theorem second_address (s : MachineData) (destination : BitVec 64)
    (words : List (BitVec 64)) (i : Nat) (previous last : BitVec 64) (flags : StatusFlags)
    (pointer : get s .r9 = destination + 8#64) :
    get (loopState s destination words i previous last flags) .r9 +
      get (loopState s destination words i previous last flags) .r10 * 8#64 =
      destination + BitVec.ofNat 64 (8*(i+1)) := by
  simp only [loopState, get, Reg64s.get64] at *
  rw [pointer]
  bv_omega

private theorem pair_image (s : MachineData) (destination : BitVec 64)
    (words : List (BitVec 64)) (i : Nat) (previous last : BitVec 64)
    (flags flags' : StatusFlags) (pointer : get s .r9 = destination + 8#64) :
    pair (loopState s destination words i previous last flags)
      (limb words i) (limb words (i+1)) flags' =
      loopState s destination words (i+2) (BitVec.ofNat 64 i) (limb words (i+1)) flags' := by
  have a := first_address s destination words i previous last flags pointer
  have b := second_address s destination words i previous last flags pointer
  unfold pair
  rw [a, b]
  simp [loopState, memory, get, Reg64s.get64, BitVec.ofNat_add]

/-- One pair transports the physical source and destination invariants. -/
theorem pair_loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (destination : BitVec 64) (words : List (BitVec 64))
    (count q i : Nat) (previous last : BitVec 64) (flags : StatusFlags)
    (bound : destination.toNat + 8*count ≤ 2^64)
    (lengthBound : words.length < 2^64) (within : i+2 ≤ q) (qBound : q ≤ count)
    (lengthReg : get s .rdx = BitVec.ofNat 64 words.length)
    (countReg : get s .rcx = BitVec.ofNat 64 q)
    (pointer : get s .r9 = destination + 8#64)
    (loads : ∀ j, j < words.length →
      Mem.loadInt s.dmem (get s .rsi + BitVec.ofNat 64 (8*j)) 8 =
        some ((limb words j).toNat : Int))
    (hm : Large.Mapped s.dmem destination (8*count))
    (apart : Large.Disjoint (get s .rsi) destination (8*words.length) (8*count))
    (P : MachineState → Prop)
    (next : ∀ flags', Eventually (step e) P
      (loopState s destination words (i+2) (BitVec.ofNat 64 i) (limb words (i+1)) flags',
        if i+2 = q then base + 729 else base + 669)) :
    Eventually (step e) P (loopState s destination words i previous last flags, base + 669) := by
  have ib : i < 2^64 := by omega
  have ib1 : i+1 < 2^64 := by omega
  have ib2 : i+2 < 2^64 := by omega
  have qb : q < 2^64 := by omega
  have firstA := first_address s destination words i previous last flags pointer
  have secondA := second_address s destination words i previous last flags pointer
  have sourceA : get (loopState s destination words i previous last flags) .rsi +
      get (loopState s destination words i previous last flags) .r10 * 8#64 =
      get s .rsi + BitVec.ofNat 64 (8*i) := by
    simp [loopState, get, Reg64s.get64, BitVec.ofNat_mul, Nat.mul_comm]
  have sourceB : get (loopState s destination words i previous last flags) .rsi +
      get (loopState s destination words i previous last flags) .r10 * 8#64 + 8#64 =
      get s .rsi + BitVec.ofNat 64 (8*(i+1)) := by
    simp only [loopState, get, Reg64s.get64]
    bv_omega
  have firstTest : (get (loopState s destination words i previous last flags) .r10).toNat <
      (get (loopState s destination words i previous last flags) .rdx).toNat ↔ i < words.length := by
    change (BitVec.ofNat 64 i).toNat < (get s .rdx).toNat ↔ _
    rw [lengthReg]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt lengthBound]
  have secondTest : (get (loopState s destination words i previous last flags) .r10 + 1#64).toNat <
      (get (loopState s destination words i previous last flags) .rdx).toNat ↔ i+1 < words.length := by
    change (BitVec.ofNat 64 i + 1#64).toNat < (get s .rdx).toNat ↔ _
    rw [lengthReg, ← BitVec.ofNat_add]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ib1, Nat.mod_eq_of_lt lengthBound]
  apply pair_cps e base hc _ (limb words i) (limb words (i+1))
  · intro present
    rw [sourceA]
    rw [show (loopState s destination words i previous last flags).dmem =
      memory s.dmem destination words i from rfl,
      memory_source s.dmem (get s .rsi) destination words count i (by omega) apart i
        (firstTest.mp present)]
    exact loads i (firstTest.mp present)
  · intro missing
    exact limb_missing words i (Nat.le_of_not_gt (fun h => missing (firstTest.mpr h)))
  · rw [firstA]
    exact Large.mapped_load _ destination (8*count) (8*i) 8
      (memory_mapped s.dmem destination destination words i (8*count) hm) (by omega)
  · intro present
    rw [firstA, sourceB]
    change Mem.loadInt (memory s.dmem destination words (i+1)) _ 8 = _
    rw [memory_source s.dmem (get s .rsi) destination words count (i+1)
      (by omega) apart (i+1) (secondTest.mp present)]
    exact loads (i+1) (secondTest.mp present)
  · intro missing
    exact limb_missing words (i+1) (Nat.le_of_not_gt (fun h => missing (secondTest.mpr h)))
  · rw [firstA, secondA]
    exact Large.mapped_load _ destination (8*count) (8*(i+1)) 8
      (memory_mapped s.dmem destination destination words (i+1) (8*count) hm) (by omega)
  · intro flags'
    rw [pair_image s destination words i previous last flags flags' pointer]
    have eq : get (loopState s destination words i previous last flags) .r10 + 2#64 =
        get (loopState s destination words i previous last flags) .rcx ↔ i+2 = q := by
      change BitVec.ofNat 64 i + 2#64 = get s .rcx ↔ _
      rw [countReg]
      bv_omega
    simpa only [eq] using next flags'

/-- Unbounded induction over the remaining pairs, reaching the real pair exit.
No restriction is imposed on arena capacity; the bound is the physical written span. -/
theorem loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (destination : BitVec 64) (words : List (BitVec 64))
    (count q : Nat) (bound : destination.toNat + 8*count ≤ 2^64)
    (lengthBound : words.length < 2^64) (qBound : q ≤ count)
    (lengthReg : get s .rdx = BitVec.ofNat 64 words.length)
    (countReg : get s .rcx = BitVec.ofNat 64 q)
    (pointer : get s .r9 = destination + 8#64)
    (loads : ∀ j, j < words.length →
      Mem.loadInt s.dmem (get s .rsi + BitVec.ofNat 64 (8*j)) 8 =
        some ((limb words j).toNat : Int))
    (hm : Large.Mapped s.dmem destination (8*count))
    (apart : Large.Disjoint (get s .rsi) destination (8*words.length) (8*count))
    (P : MachineState → Prop)
    (next : ∀ last flags, Eventually (step e) P
      (loopState s destination words q (BitVec.ofNat 64 (q-2)) last flags, base + 729)) :
    ∀ i, i < q → (q-i)%2 = 0 → ∀ previous last flags,
      Eventually (step e) P (loopState s destination words i previous last flags, base + 669) := by
  intro i
  induction remaining : q-i using Nat.strongRecOn generalizing i with
  | ind n ih =>
    intro before even previous last flags
    have within : i+2 ≤ q := by omega
    apply pair_loop_cps e base hc s destination words count q i previous last flags
      bound lengthBound within qBound lengthReg countReg pointer loads hm apart P
    intro flags'
    by_cases done : i+2 = q
    · simp only [done, ↓reduceIte]
      have index : i = q-2 := by omega
      simpa only [done, index] using next (limb words (i+1)) flags'
    · simp only [done, ↓reduceIte]
      exact ih (q-(i+2)) (by omega) (i+2) rfl (by omega) (by omega) _ _ flags'

end SszX86.NatDivision.Copy
