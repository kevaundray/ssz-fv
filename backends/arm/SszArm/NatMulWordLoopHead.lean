import SszArm.NatMulWordLoopFrame
import SszArm.NatMulWordScanFrame
import SszArm.WordNormalize

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
    Udivti3.next, state_simp_rules, Udivti3.cmp_carry]
  simp only [← Nat.not_lt, ite_not]

theorem loop_head_stable (s : ArmState) (base : BitVec 64) :
    LoopStable s (loopHead s base) := by
  refine ⟨by simp [loopHead], by simp [loopHead], ?_, ?_⟩
  · intro reg keep
    exact loop_head_registers s base reg (by simp_all)
  · intro reg
    exact loop_block_vectors base loopHeadOps s reg

private theorem input_loaded_gpr (s : ArmState) (base value : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (loaded .input s base value) =
      if reg = 17#5 then value else r (.GPR reg) s := by
  simp only [loaded, LoadSite.destination, NatCompare.r_gpr_of_w_pc,
    NatCompare.r_gpr_of_w_gpr, NatCompare.saved, r_of_write_mem_bytes]

private theorem input_loaded_field (s : ArmState) (base value : BitVec 64)
    (field : StateField) (pc : field ≠ .PC) (destination : field ≠ .GPR 17#5) :
    r field (loaded .input s base value) = r field s := by
  simp only [loaded, LoadSite.destination, r_of_w_different pc,
    r_of_w_different destination, NatCompare.saved, r_of_write_mem_bytes]

private theorem input_loaded_program (s : ArmState) (base value : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    (loaded .input s base value).program = s.program := by
  simpa only [loaded, w_program, LoadSite.scratch] using
    (NatCompare.saved_frame s 9#5 stack).program

private theorem input_loaded_pc (s : ArmState) (base value : BitVec 64) :
    read_pc (loaded .input s base value) = base + 632#64 := by
  simp only [loaded, read_pc, r_of_w_same, LoadSite.start] <;> arm_word_nf

private theorem input_loaded_memory (s : ArmState) (base value : BitVec 64) :
    (loaded .input s base value).mem = (NatCompare.saved s 9#5).mem := by
  simp only [loaded, ArmState.mem_w_eq_mem, LoadSite.scratch]

private theorem loop_zero_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p824, .p828] s) =
      if reg = 17#5 then 0#64 else r (.GPR reg) s := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
    NatCompare.r_gpr_of_w_pc, NatCompare.r_gpr_of_w_gpr] <;> arm_word_nf

private theorem loop_zero_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p824, .p828] s) = base + 632#64 := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, read_pc, r_of_w_same]

private theorem loop_zero_memory (s : ArmState) (base : BitVec 64) :
    (block base [.p824, .p828] s).mem = s.mem := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, ArmState.mem_w_eq_mem]

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
  have stable : LoopStable s u := loop_head_stable s base
  have sp : r (.GPR 31#5) u = r (.GPR 31#5) s := stable.sp
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
  have pure : u.mem = s.mem := loop_head_memory s base
  have keepU : ∀ reg : BitVec 5, reg ≠ 16#5 → r (.GPR reg) u = r (.GPR reg) s :=
    loop_head_registers s base
  by_cases inside : index < words.length
  · have upc : read_pc u = base + 600#64 := by
      rw [loop_head_pc, nextNat, lengthNat, if_pos inside]
    have address : LoadSite.input.address u = pointer + (BitVec.ofNat 64 index <<< 3) := by
      change r (.GPR 1#5) u + (r (.GPR 13#5) u <<< 3) = _
      rw [keepU 1#5 (by decide), keepU 13#5 (by decide), pointerReg, indexReg]
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
      exact (show r (.GPR reg) t = r (.GPR reg) u by
        rw [input_loaded_gpr, if_neg h17]).trans (keepU reg h16)
    have finalStable : LoopStable s t := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (input_loaded_program u base _ (by rw [sp]; exact source.1)).trans stable.program
      · exact (input_loaded_field u base _ .ERR (by decide) (by decide)).trans stable.error
      · intro reg different
        exact keep reg (by simp_all) (by simp_all)
      · intro reg
        exact (input_loaded_field u base _ (.SFP reg)
          (by intro h; cases h) (by intro h; cases h)).trans (stable.vectors reg)
    refine ⟨3 + 8, t, by rw [run_plus, before, hr], finalStable, ?_, ?_, ?_, keep, ?_⟩
    · exact input_loaded_pc u base _
    · exact (show r (.GPR 16#5) t = r (.GPR 16#5) u by
        rw [input_loaded_gpr, if_neg (by decide)]).trans indexU
    · exact (show r (.GPR 17#5) t = words[index]?.getD 0#64 by
        rw [input_loaded_gpr, if_pos rfl])
    · intro a outside
      have apart := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
      have savedFrame := NatCompare.saved_frame u 9#5 (by rw [sp]; exact source.1)
      have preserved := savedFrame.memory a (by
        rw [sp]
        simp only [Prod.fst, Prod.snd] at apart
        omega)
      exact (congrFun (input_loaded_memory u base _) a).trans
        (preserved.trans (congrFun pure a))
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
      exact (show r (.GPR reg) t = r (.GPR reg) u by
        rw [loop_zero_gpr, if_neg h17]).trans (keepU reg h16)
    have finalStable : LoopStable s t := by
      refine ⟨(block_program _ _ _).trans stable.program,
        (block_error _ _ _).trans stable.error, ?_, ?_⟩
      · intro reg different
        exact keep reg (by simp_all) (by simp_all)
      · intro reg
        exact (loop_block_vectors _ _ _ _).trans (stable.vectors reg)
    refine ⟨3 + 2, t, by rw [run_plus, before, zeroRun], finalStable, ?_, ?_, ?_, keep, ?_⟩
    · exact loop_zero_pc u base
    · exact (show r (.GPR 16#5) t = r (.GPR 16#5) u by
        rw [loop_zero_gpr, if_neg (by decide)]).trans indexU
    · rw [loop_zero_gpr, if_pos rfl,
        List.getElem?_eq_none (by omega : words.length ≤ index), Option.getD_none]
    · intro a _
      exact congrFun ((loop_zero_memory u base).trans pure) a

end SszArm.NatMulWord
