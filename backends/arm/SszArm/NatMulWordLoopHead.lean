import SszArm.NatMulWordLoopFrame
import SszArm.NatMulWordScanFrame

namespace SszArm.NatMulWord

open Delimited (MemoryFrame)

def loopHeadOps : List Op := [.p812, .p816, .p820]

def loopHead (s : ArmState) (base : BitVec 64) : ArmState := block base loopHeadOps s

theorem loop_head_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 812#64) : run 3 s = loopHead s base := by
  apply block_run base loopHeadOps s code error aligned
  have hpc : r .PC s = base + 812#64 := pc
  simp [loopHeadOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

theorem loop_head_registers (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (keep : reg ≠ 16#5) :
    r (.GPR reg) (loopHead s base) = r (.GPR reg) s := by
  simp [loopHead, loopHeadOps, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, keep]

theorem loop_head_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 16#5) (loopHead s base) = r (.GPR 13#5) s + 1#64 := by
  simp [loopHead, loopHeadOps, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules]

theorem loop_head_memory (s : ArmState) (base : BitVec 64) :
    (loopHead s base).mem = s.mem := by
  simp [loopHead, loopHeadOps, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules]

theorem loop_head_pc (s : ArmState) (base : BitVec 64) :
    read_pc (loopHead s base) =
      if (r (.GPR 13#5) s + 1#64).toNat < (r (.GPR 2#5) s).toNat
      then base + 600#64 else base + 824#64 := by
  simp [loopHead, loopHeadOps, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, Udivti3.cmp_carry, Nat.not_le]

theorem loop_head_stable (s : ArmState) (base : BitVec 64) :
    LoopStable s (loopHead s base) := by
  refine ⟨by simp [loopHead], by simp [loopHead], ?_, ?_⟩
  · intro reg keep
    exact loop_head_registers s base reg (by simp_all)
  · intro reg
    exact loop_block_vectors base loopHeadOps s reg

/-- Both native choices at812: the indexed load uses the postincremented raw
pointer, and out-of-range access follows824/828 without reading memory. -/
theorem loop_input_runs (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (index : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 812#64)
    (positive : 0 < index) (indexBound : index < 2^64)
    (pointerReg : r (.GPR 1#5) s = pointer + 8#64)
    (lengthReg : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (indexReg : r (.GPR 13#5) s = BitVec.ofNat 64 (index - 1))
    (source : NatCompare.Source s pointer words) (current : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ LoopStable s t ∧ read_pc t = base + 632#64 ∧
      r (.GPR 16#5) t = BitVec.ofNat 64 index ∧
      r (.GPR 17#5) t = words[index]?.getD 0#64 ∧
      (∀ reg : BitVec 5, reg ≠ 16#5 → reg ≠ 17#5 → r (.GPR reg) t = r (.GPR reg) s) ∧
      MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s t := by
  let u := loopHead s base
  have stable := loop_head_stable s base
  have sp := stable.sp
  have nextIndex : r (.GPR 13#5) s + 1#64 = BitVec.ofNat 64 index := by
    rw [indexReg]
    have : index - 1 + 1 = index := by omega
    simpa only [BitVec.ofNat_add] using congrArg (BitVec.ofNat 64) this
  have nextNat : (r (.GPR 13#5) s + 1#64).toNat = index := by
    rw [nextIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
  have lengthBound : words.length < 2^64 := by have h := source.2.1; omega
  have lengthNat : (r (.GPR 2#5) s).toNat = words.length := by
    rw [lengthReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound]
  have indexU : r (.GPR 16#5) u = BitVec.ofNat 64 index :=
    (loop_head_index s base).trans nextIndex
  have before := loop_head_run s base code error aligned pc
  have pure := loop_head_memory s base
  have keepU := loop_head_registers s base
  by_cases inside : index < words.length
  · have upc : read_pc u = base + 600#64 := by
      rw [loop_head_pc, nextNat, lengthNat, if_pos inside]
    have address : LoadSite.input.address u = pointer + (BitVec.ofNat 64 index <<< 3) := by
      simp only [LoadSite.address, loop_head_registers _ _ _ (by decide), pointerReg, indexReg]
      bv_omega
    have observed := scan_limb s pointer words index inside source current
    have physical : (LoadSite.input.address u).toNat + 8 ≤ 2^64 := by
      rw [address]; exact observed.1
    have separate : (LoadSite.input.address u).toNat + 8 ≤ (r (.GPR 31#5) u).toNat - 16 ∨
        (r (.GPR 31#5) u).toNat ≤ (LoadSite.input.address u).toNat := by
      rw [address, sp]; exact observed.2.1
    have atU : read_mem_bytes 8 (LoadSite.input.address u) u = words[index]?.getD 0#64 := by
      rw [address, Memory.mem_eq_iff_read_mem_bytes_eq.mp pure]
      exact observed.2.2
    have hr := load_run .input u base (words[index]?.getD 0#64)
      (stable.code code) (stable.error.trans error) (stable.aligned aligned) upc
      (by rw [sp]; exact source.1) physical separate atU
    let t := loaded .input u base (words[index]?.getD 0#64)
    have keep : ∀ reg : BitVec 5, reg ≠ 16#5 → reg ≠ 17#5 →
        r (.GPR reg) t = r (.GPR reg) s := by
      intro reg h16 h17
      simpa only [t, loaded, LoadSite.destination, NatCompare.saved, state_simp_rules,
        h17, ↓reduceIte] using keepU reg h16
    have finalStable : LoopStable s t := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [t, loaded, NatCompare.saved, state_simp_rules, stable.program]
      · simp only [t, loaded, NatCompare.saved, state_simp_rules, stable.error]
      · intro reg different
        exact keep reg (by simp_all) (by simp_all)
      · intro reg
        simpa only [t, loaded, NatCompare.saved, state_simp_rules] using stable.vectors reg
    refine ⟨3 + 8, t, by rw [run_plus, before, hr], finalStable, ?_, ?_, ?_, keep, ?_⟩
    · simp [t, loaded, LoadSite.start, state_simp_rules]
    · simpa [t, loaded, LoadSite.destination, NatCompare.saved, state_simp_rules] using indexU
    · simp [t, loaded, LoadSite.destination, state_simp_rules]
    · intro a outside
      have apart := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
      have savedFrame := NatCompare.saved_frame u 9#5 (by rw [sp]; exact source.1)
      have preserved := savedFrame.memory a (by
        rw [sp]
        simp only [Prod.fst, Prod.snd] at apart
        omega)
      simpa only [t, loaded, state_simp_rules] using preserved.trans (congrFun pure a)
  · have upc : read_pc u = base + 824#64 := by
      rw [loop_head_pc, nextNat, lengthNat, if_neg inside]
    have zeroRun : run 2 u = block base [.p824, .p828] u := by
      apply block_run base [.p824, .p828] u (stable.code code)
        (stable.error.trans error) (stable.aligned aligned)
      have hpc : r .PC u = base + 824#64 := upc
      simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
    let t := block base [.p824, .p828] u
    have keep : ∀ reg : BitVec 5, reg ≠ 16#5 → reg ≠ 17#5 →
        r (.GPR reg) t = r (.GPR reg) s := by
      intro reg h16 h17
      simpa [t, block, Op.effect, put, next, state_simp_rules, h17] using keepU reg h16
    have finalStable : LoopStable s t := by
      refine ⟨by simp [t, stable.program], by simp [t, stable.error], ?_, ?_⟩
      · intro reg different
        exact keep reg (by simp_all) (by simp_all)
      · intro reg
        exact (loop_block_vectors _ _ _ _).trans (stable.vectors reg)
    refine ⟨3 + 2, t, by rw [run_plus, before, zeroRun], finalStable, ?_, ?_, ?_, keep, ?_⟩
    · simp [t, block, Op.effect, put, next, state_simp_rules]
    · simpa [t, block, Op.effect, put, next, state_simp_rules] using indexU
    · simp [t, block, Op.effect, put, next, state_simp_rules,
        List.getElem?_eq_none (by omega : words.length ≤ index)]
    · intro a _
      simpa [t, block, Op.effect, put, next, state_simp_rules] using congrFun pure a

end SszArm.NatMulWord
