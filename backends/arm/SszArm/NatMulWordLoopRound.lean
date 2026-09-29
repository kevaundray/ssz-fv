import SszArm.NatMulWordLoopHead

namespace SszArm.NatMulWord

open Delimited (Protected MemoryFrame)
open NatCompare (Words)

/-- Current register facts at the actual812 loop head. -/
structure LoopHeadAt (s : ArmState) (base raw pointer factor : BitVec 64)
    (words : List (BitVec 64)) (count index : Nat) : Prop where
  pc : read_pc s = base + 812#64
  rawPointer : r (.GPR 1#5) s = raw + 8#64
  rawLength : r (.GPR 2#5) s = BitVec.ofNat 64 words.length
  factorReg : r (.GPR 3#5) s = factor
  countReg : r (.GPR 9#5) s = BitVec.ofNat 64 count
  indexReg : r (.GPR 13#5) s = BitVec.ofNat 64 (index - 1)
  outputNext : r (.GPR 15#5) s = pointer + 8#64

theorem loop_source (s : ArmState) (raw pointer : BitVec 64)
    (words : List (BitVec 64)) (count : Nat)
    (space : NatMul.LoopSpace (r (.GPR 31#5) s) pointer count)
    (physical : raw.toNat + 8 * words.length ≤ 2^64)
    (separate : Protected (NatMul.loopWrites (r (.GPR 31#5) s) pointer count)
      raw.toNat (8 * words.length)) : NatCompare.Source s raw words := by
  refine ⟨by
    have stack := space.stack
    arm_word_nf at stack ⊢
    omega, physical, ?_⟩
  rcases separate with empty | separate
  · left
    apply List.eq_nil_of_length_eq_zero
    omega
  · right
    have apart := separate ((r (.GPR 31#5) s).toNat - 48, 48) (by simp [NatMul.loopWrites])
    have stack := space.stack
    simp only [Prod.fst, Prod.snd] at apart
    change raw.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ raw.toNat
    omega

/-- One real head/load/product/store/carry/compare iteration appends exactly
one newly observed word, never requiring an initialized destination suffix. -/
theorem loop_round_runs (s : ArmState) (base raw pointer factor : BitVec 64)
    (words doneWords : List (BitVec 64)) (count index : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (head : LoopHeadAt s base raw pointer factor words count index)
    (positive : 0 < index) (within : index ≤ count) (prefixLength : doneWords.length = index)
    (space : NatMul.LoopSpace (r (.GPR 31#5) s) pointer (count + 1))
    (physical : raw.toNat + 8 * words.length ≤ 2^64)
    (separate : Protected (NatMul.loopWrites (r (.GPR 31#5) s) pointer (count + 1))
      raw.toNat (8 * words.length))
    (input : Words s raw words) (written : Words s pointer doneWords) :
    let next := SszNative.LimbMul.step factor (words[index]?.getD 0#64) 0#64
      (r (.GPR 14#5) s).toNat
    ∃ fuel t, run fuel s = t ∧ LoopStable s t ∧
      read_pc t = (if index = count then base + 1464#64 else base + 812#64) ∧
      r (.GPR 13#5) t = BitVec.ofNat 64 index ∧ (r (.GPR 14#5) t).toNat = next.2 ∧
      Words t pointer (doneWords ++ [next.1]) ∧
      MemoryFrame (NatMul.loopWrites (r (.GPR 31#5) s) pointer (count + 1)) s t := by
  dsimp only
  have countBound : count < 2^64 := by have h := space.physical; omega
  have indexBound : index < 2^64 := by omega
  have source := loop_source s raw pointer words (count + 1) space physical separate
  obtain ⟨fuel, u, hu, stable, upc, u16, u17, keep, frame⟩ :=
    loop_input_runs s base raw words index code error aligned head.pc positive indexBound
      head.rawPointer head.rawLength head.indexReg source input
  have u13 := (keep 13#5 (by decide) (by decide)).trans head.indexReg
  have u15 := (keep 15#5 (by decide) (by decide)).trans head.outputNext
  have u3 := (keep 3#5 (by decide) (by decide)).trans head.factorReg
  have u9 := (keep 9#5 (by decide) (by decide)).trans head.countReg
  have u14 := keep 14#5 (by decide) (by decide)
  have address : roundAddress u = pointer + BitVec.ofNat 64 (8 * index) := by
    unfold roundAddress
    rw [u15, u13]
    bv_omega
  have addressNat := space.address (by omega : index < count + 1)
  have stackU : 48 ≤ (r (.GPR 31#5) u).toNat := by rw [stable.sp]; exact space.stack
  have cellPhysical : (roundAddress u).toNat + 8 ≤ 2^64 := by
    rw [address, addressNat]
    have h := space.physical
    omega
  have cellSeparate : (roundAddress u).toNat + 8 ≤ (r (.GPR 31#5) u).toNat - 48 ∨
      (r (.GPR 31#5) u).toNat ≤ (roundAddress u).toNat := by
    rw [address, addressNat, stable.sp]
    have h := space.apart
    omega
  let t := roundCompleted u base
  have roundRun := round_run u base (stable.code code) (stable.error.trans error)
    (stable.aligned aligned) upc
  have roundStable := round_completed_stable u base stackU cellPhysical cellSeparate
  have memory := round_completed_memory u base stackU cellPhysical cellSeparate
  have stepEq := round_completed_step u base stackU cellPhysical cellSeparate
  rw [u3, u17, u14] at stepEq
  have low := congrArg Prod.fst stepEq
  have carry := congrArg Prod.snd stepEq
  have cellFrame : MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48),
      ((pointer + BitVec.ofNat 64 (8 * index)).toNat, 8)] s t := by
    intro a outside
    have after := memory.1 a (by simpa only [stable.sp, address] using outside)
    apply after.trans
    apply frame a
    intro span member
    simp only [List.mem_singleton] at member
    exact outside span (by simp only [List.mem_cons, member, true_or])
  have stored : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * index)) t =
      (SszNative.LimbMul.step factor (words[index]?.getD 0#64) 0#64 (r (.GPR 14#5) s).toNat).1 := by
    rw [← address]
    exact memory.2.trans low
  have appended := NatMul.words_snoc_of_frame
    (space.prefix (by rw [prefixLength]; omega)) written
    (by simpa only [prefixLength] using cellFrame) (by simpa only [prefixLength] using stored)
  have compare : (r (.GPR 9#5) u = r (.GPR 16#5) u) ↔ index = count := by
    rw [u9, u16]
    constructor
    · intro h
      have hnat := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound,
        Nat.mod_eq_of_lt indexBound] at hnat
      exact hnat.symm
    · intro h
      rw [h]
  refine ⟨fuel + roundFuel u base, t, by rw [run_plus, hu, roundRun],
    stable.trans roundStable, ?_, ?_, carry, appended,
    NatMul.loopFrame_of_cell space index (by omega) cellFrame⟩
  · rw [round_completed_pc u base stackU cellPhysical cellSeparate]
    simp only [compare]
  · exact (round_completed_index u base stackU cellPhysical cellSeparate).trans u16

end SszArm.NatMulWord
