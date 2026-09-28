import SszX86.EmitUintLoopFacts

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open SszNative
open BoolCodec UintCodec
open UintCodec.Large (get)

theorem small_pair_inv (original current : MachineData) (limb : BitVec 64)
    (count index : Nat) (flags : StatusFlags)
    (owned : LoopOwned original (.small limb) count)
    (inv : LoopInv original current (.small limb) count index)
    (even : index % 2 = 0) (within : index + 2 ≤ count) :
    LoopInv original (smallPair current flags) (.small limb) count (index + 2) := by
  have physical : index < 2 ^ 64 := by have := owned.bounded; omega
  have low : (get current .rax).toNat = index := by
    rw [inv.indexReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
  have selected : (if (get current .rax).toNat < 8 then get current .rdx else 0) =
      ((NatOperand.small limb).words[index / 8]?.getD 0) := by
    rw [low, inv.payload]
    exact (small_limb limb index).symm
  refine ⟨inv.stack, inv.result, inv.output, inv.vector, inv.length, ?_, ?_, inv.payload,
    inv.source, trivial, ?_, ?_⟩
  · change get current .rax + 2#64 = _
    rw [inv.indexReg, BitVec.ofNat_add]
  · change get current .r9 + BitVec.ofNat 64 (8 * 2) = _
    rw [inv.counter]
    simp only [Nat.mul_add, BitVec.ofNat_add]
  · intro positive
    change get current .rax = BitVec.ofNat 64 (index + 2 - 2)
    simpa only [Nat.add_sub_cancel] using inv.indexReg
  · change Prefix _ (pairMemory current _) _ _ _
    rw [selected]
    exact pair_prefix original current (.small limb) count index owned inv even within

theorem large_pair_inv (original current : MachineData) (pointer : BitVec 64)
    (limbs : List (BitVec 64)) (count index : Nat) (flags : StatusFlags)
    (owned : LoopOwned original (.large pointer limbs) count)
    (inv : LoopInv original current (.large pointer limbs) count index)
    (even : index % 2 = 0) (within : index + 2 ≤ count) :
    LoopInv original (largePair current (limbs[index / 8]?.getD 0) flags)
      (.large pointer limbs) count (index + 2) := by
  refine ⟨inv.stack, inv.result, inv.output, inv.vector, inv.length, ?_, ?_, inv.payload,
    inv.source, inv.limit, trivial, ?_⟩
  · change get current .rax + 2#64 = _
    rw [inv.indexReg, BitVec.ofNat_add]
  · change get current .r9 + BitVec.ofNat 64 (8 * 2) = _
    rw [inv.counter]
    simp only [Nat.mul_add, BitVec.ofNat_add]
  · exact pair_prefix original current (.large pointer limbs) count index owned inv even within

/-- Small uses the actual CMOV pair loop for every number of zero-extension
bytes. Induction is over remaining bytes, not a finite width enumeration. -/
theorem small_loop_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original : MachineData) (limb : BitVec 64) (count : Nat)
    (owned : LoopOwned original (.small limb) count) (P : MachineState → Prop)
    (next : ∀ current, LoopInv original current (.small limb) count (2 * (count / 2)) →
      Eventually (step e) P (current, base + 1113)) :
    ∀ index current, index % 2 = 0 → index < 2 * (count / 2) →
      LoopInv original current (.small limb) count index →
      Eventually (step e) P (current, base + 1056) := by
  intro index
  induction remaining : 2 * (count / 2) - index using Nat.strongRecOn generalizing index with
  | ind left ih =>
    intro current even before inv
    have within : index + 2 ≤ count := by omega
    have physical : index + 2 < 2 ^ 64 := by have := owned.bounded; omega
    have indexNat : current.regs.rax.toNat = index := by
      have equal := congrArg BitVec.toNat inv.indexReg
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index < 2 ^ 64)] using equal
    apply small_pair_runs e base hc current count P
    · rw [inv.output]
      simpa only [Limbs.bytes, Array.size_ofFn] using
        prefix_mapped inv.hprefix
          (by simpa only [Limbs.bytes, Array.size_ofFn] using owned.outputMapped)
          (by simpa only [Limbs.bytes, Array.size_ofFn] using Nat.le_of_lt owned.bounded)
    · omega
    · intro flags
      have advanced := small_pair_inv original current limb count index flags owned inv even within
      have branch : get current .rdi = get current .rax + 2 ↔ index + 2 = 2 * (count / 2) := by
        have source : get current .rdi = BitVec.ofNat 64 (2 * (count / 2)) := inv.source
        rw [source, inv.indexReg]
        simp only [BitVec.ofNat_eq_ofNat]
        rw [← BitVec.ofNat_add]
        constructor
        · intro equal
          have values := congrArg BitVec.toNat equal
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by have := owned.bounded; omega : 2 * (count / 2) < 2 ^ 64),
            Nat.mod_eq_of_lt physical] at values
          omega
        · intro equal
          rw [equal]
      by_cases last : index + 2 = 2 * (count / 2)
      · rw [ite_eq_left (branch.mpr last)]
        apply next
        simpa only [last] using advanced
      · rw [ite_eq_right (fun equal => last (branch.mp equal))]
        exact ih (2 * (count / 2) - (index + 2)) (by omega) (index + 2) rfl
          (smallPair current flags) (by omega) (by omega) advanced

/-- Large uses each original padded limb while present, then its real zero-fill
edge. No relation between physical limb count and output width is assumed. -/
theorem large_loop_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original : MachineData) (pointer : BitVec 64) (limbs : List (BitVec 64)) (count : Nat)
    (owned : LoopOwned original (.large pointer limbs) count) (P : MachineState → Prop)
    (next : ∀ current, LoopInv original current (.large pointer limbs) count (2 * (count / 2)) →
      Eventually (step e) P (current, base + 1002)) :
    ∀ index current, index % 2 = 0 → index < 2 * (count / 2) →
      LoopInv original current (.large pointer limbs) count index →
      Eventually (step e) P (current, base + 946) := by
  intro index
  induction remaining : 2 * (count / 2) - index using Nat.strongRecOn generalizing index with
  | ind left ih =>
    intro current even before inv
    have within : index + 2 ≤ count := by omega
    have physical : index + 2 < 2 ^ 64 := by have := owned.bounded; omega
    have indexNat : (get current .rax).toNat = index := by
      rw [inv.indexReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index < 2 ^ 64)]
    have countPhysical : limbs.length < 2 ^ 64 := by have := owned.operand.2.2.1; omega
    have lengthNat : (get current .rdx).toNat = limbs.length := by
      rw [inv.payload]
      exact Nat.mod_eq_of_lt countPhysical
    apply large_pair_runs e base hc current (limbs[index / 8]?.getD 0) count P
    · rw [inv.output]
      simpa only [Limbs.bytes, Array.size_ofFn] using
        prefix_mapped inv.hprefix
          (by simpa only [Limbs.bytes, Array.size_ofFn] using owned.outputMapped)
          (by simpa only [Limbs.bytes, Array.size_ofFn] using Nat.le_of_lt owned.bounded)
    · change (get current .rax).toNat + 2 ≤ count
      rw [indexNat]
      exact within
    · intro inside
      rw [indexNat, lengthNat] at inside
      rw [indexNat, inv.source]
      exact loop_limb original current pointer limbs count index (index / 8) owned inv inside
    · intro outside
      rw [indexNat, lengthNat] at outside
      simp [List.getElem?_eq_none outside]
    · intro inside a ha equal
      rw [indexNat, lengthNat] at inside
      rw [indexNat, inv.source, inv.indexReg] at equal
      have outputReg : get current .r14 = original.regs.r14.toBitVec := by
        simp only [UintCodec.Large.get, Reg64s.get64, inv.output]
      rw [outputReg] at equal
      apply owned.readGuard (pointer + BitVec.ofNat 64 (8 * (index / 8)) + BitVec.ofNat 64 a)
      · exact Bits.span_subspan pointer (8 * (index / 8)) 8 (8 * limbs.length) (by omega) ⟨a, ha, rfl⟩
      · exact ⟨index, by omega, equal⟩
    · intro flags
      have advanced := large_pair_inv original current pointer limbs count index flags owned inv even within
      have branch : get current .r8 = get current .rax + 2 ↔ index + 2 = 2 * (count / 2) := by
        have limit : get current .r8 = BitVec.ofNat 64 (2 * (count / 2)) := inv.limit
        rw [limit, inv.indexReg]
        simp only [BitVec.ofNat_eq_ofNat]
        rw [← BitVec.ofNat_add]
        constructor
        · intro equal
          have values := congrArg BitVec.toNat equal
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by have := owned.bounded; omega : 2 * (count / 2) < 2 ^ 64),
            Nat.mod_eq_of_lt physical] at values
          omega
        · intro equal
          rw [equal]
      by_cases last : index + 2 = 2 * (count / 2)
      · rw [ite_eq_left (branch.mpr last)]
        apply next
        simpa only [last] using advanced
      · rw [ite_eq_right (fun equal => last (branch.mp equal))]
        exact ih (2 * (count / 2) - (index + 2)) (by omega) (index + 2) rfl
          (largePair current (limbs[index / 8]?.getD 0) flags) (by omega) (by omega) advanced

end SszX86.Emit.Uint
