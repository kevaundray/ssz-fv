import SszArm.NatMulLoopStages

namespace SszArm.NatMul

/-- The carry guard, next-row comparison/pointer update, actual indexed carry
store and +1008 backedge. In particular, the carry is an overwrite. -/
theorem loop_row_finish_run (s : ArmState) (base dst carry : BitVec 64)
    (left right row : Nat) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 952#64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : dst.toNat + 8 * (left + right) ≤ 2^64)
    (separate : dst.toNat + 8 * (left + right) ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ dst.toNat)
    (inside : row < left)
    (r12 : r (.GPR 12#5) s = BitVec.ofNat 64 row)
    (r13 : r (.GPR 13#5) s = BitVec.ofNat 64 (row + 1))
    (r19 : r (.GPR 19#5) s = BitVec.ofNat 64 (left + right))
    (r20 : r (.GPR 20#5) s = dst)
    (r21 : r (.GPR 21#5) s = BitVec.ofNat 64 left)
    (r22 : r (.GPR 22#5) s = BitVec.ofNat 64 right)
    (r11 : r (.GPR 11#5) s = dst + BitVec.ofNat 64 (8 * row))
    (r15 : r (.GPR 15#5) s = carry) :
    ∃ t, run 15 s = t ∧ LoopStable loopOuterChanged s t ∧
      Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48),
        ((dst + BitVec.ofNat 64 (8 * (row + right))).toNat, 8)] s t ∧
      read_pc t = base + (if row + 1 = left then 1012#64 else 600#64) ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 (row + 1) ∧
      r (.GPR 11#5) t = dst + BitVec.ofNat 64 (8 * (row + 1)) ∧
      read_mem_bytes 8 (dst + BitVec.ofNat 64 (8 * (row + right))) t = carry := by
  have count : left + right < 2^64 := by omega
  let g := block base [.p952, .p956, .p960] s
  have guard := carry_guard_run s base left right row code error aligned pc r12 r22 r19 count inside
  have runG : run 3 s = g := guard.1
  have gp : read_pc g = base + 964#64 := by simpa only [runG] using guard.2.1
  have g0 : r (.GPR 0#5) g = BitVec.ofNat 64 (row + right) := by simpa only [runG] using guard.2.2
  have gr (reg : BitVec 5) (different : reg ≠ 0#5) : r (.GPR reg) g = r (.GPR reg) s := by
    simp_all [g, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  have gf : LoopStable loopOuterChanged s g := by
    constructor
    · simp [g]
    · simp [g]
    · exact gr _ (by decide)
    · intro reg h; apply gr; simp_all
    · intro reg; simp [g, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  let d := loopRowAdvance base g
  have runD : run 3 g = d := loop_row_advance_run g base (gf.code code)
    (gf.error.trans error) (gf.aligned aligned) gp
  have df : LoopStable loopOuterChanged g d := by
    constructor
    · simp [d, loopRowAdvance]
    · simp [d, loopRowAdvance]
    · simp [d, loopRowAdvance, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro reg different
      simp_all [d, loopRowAdvance, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro reg
      simp [d, loopRowAdvance, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  have allD := gf.trans df
  have d0 : r (.GPR 0#5) d = BitVec.ofNat 64 (row + right) := by
    simpa [d, loopRowAdvance, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules] using g0
  have address : LoopStoreSite.carry.address d = dst + BitVec.ofNat 64 (8 * (row + right)) := by
    simp only [LoopStoreSite.address, LoopStoreSite.pointer, LoopStoreSite.index, d0,
      allD.registers 20#5 (by decide), r20]
    bv_omega
  have addressNat : (LoopStoreSite.carry.address d).toNat = dst.toNat + 8 * (row + right) := by
    rw [address]
    bv_omega
  have addressPhysical : (LoopStoreSite.carry.address d).toNat + 8 ≤ 2^64 := by rw [addressNat]; omega
  let w := loopStored .carry d base
  have runW : run 8 d = w := by
    apply loop_store_run .carry d base (allD.code code) (allD.error.trans error)
      (allD.aligned aligned)
    · simp [d, loopRowAdvance, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, gp, BitVec.add_assoc]
    · rw [allD.sp]; omega
    · exact addressPhysical
    · rw [addressNat, allD.sp]; omega
  have wf : LoopStable loopOuterChanged d w :=
    (loop_store_stable .carry base d).weaken (by intro reg member; simp_all)
  have allW := allD.trans wf
  let t := Op.p1008.effect base w
  have runT : run 1 w = t := by
    change stepi w = t
    exact step w base .p1008 (allW.code code) (loop_stored_pc .carry d base)
      (allW.error.trans error) (allW.aligned aligned)
  have tf : LoopStable loopOuterChanged w t := by
    constructor <;> simp [t, Op.effect, state_simp_rules]
  have test : BitVec.ofNat 64 (row + 1) = BitVec.ofNat 64 left ↔ row + 1 = left := by bv_omega
  refine ⟨t, ?_, allW.trans tf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 15 = 3 + 3 + 8 + 1 by decide, run_plus, run_plus, run_plus, runG, runD, runW, runT]
  · intro a outside
    have stackOut := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
    have wordOut := outside ((dst + BitVec.ofNat 64 (8 * (row + right))).toNat, 8) (by simp)
    have frame := loop_stored_frame .carry d base (by rw [allD.sp]; omega) addressPhysical
    have preserved := frame a (by
      intro span member
      simp only [List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl
      · rw [allD.sp]; omega
      · rw [address]; exact wordOut)
    simpa [t, d, g, loopRowAdvance, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules] using preserved
  · simp [t, Op.effect, state_simp_rules, loop_stored_flags, d, loopRowAdvance,
      block, put, next, Udivti3.compare, Udivti3.next, gr, r13, r21, Udivti3.cmp_zero, test]
  · simp [t, Op.effect, state_simp_rules, loop_stored_registers, d, loopRowAdvance,
      block, put, next, Udivti3.compare, Udivti3.next, gr, r13]
  · simp [t, Op.effect, state_simp_rules, loop_stored_registers, d, loopRowAdvance,
      block, put, next, Udivti3.compare, Udivti3.next, gr, r11]
    bv_omega
  · have observed := loop_stored_word .carry d base addressPhysical
    rw [address] at observed
    simpa [t, Op.effect, state_simp_rules, d, loopRowAdvance, block, put, next,
      Udivti3.compare, Udivti3.next, gr, r15] using observed

end SszArm.NatMul
