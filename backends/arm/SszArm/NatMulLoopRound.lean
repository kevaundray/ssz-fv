import SszArm.NatMulLoopStages

namespace SszArm.NatMul

open Delimited (MemoryFrame)

/-- One complete real inner iteration. The only memory observations are at
entry; in particular the destination word and both lowering spills are proved. -/
theorem loop_round_run (s : ArmState) (base : BitVec 64)
    (left right i j : Nat) (a word old carry : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 680#64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (allocation : (r (.GPR 20#5) s).toNat + 8 * (left + right) ≤ 2^64)
    (row : r (.GPR 12#5) s = BitVec.ofNat 64 i)
    (column : r (.GPR 16#5) s = BitVec.ofNat 64 j)
    (count : r (.GPR 19#5) s = BitVec.ofNat 64 (left + right))
    (width : r (.GPR 25#5) s = BitVec.ofNat 64 right)
    (leftIndex : i < left) (rightIndex : j < right)
    (factor : r (.GPR 14#5) s = a) (incoming : r (.GPR 15#5) s = carry)
    (zero : r (.GPR 17#5) s = 0#64)
    (sourcePhysical : (LoopLoadSite.right.address s).toNat + 8 ≤ 2^64)
    (sourceSeparate : (LoopLoadSite.right.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (LoopLoadSite.right.address s).toNat)
    (outputPhysical : (LoopStoreSite.output.address s).toNat + 8 ≤ 2^64)
    (outputSeparate : (LoopStoreSite.output.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (LoopStoreSite.output.address s).toNat)
    (source : read_mem_bytes 8 (LoopLoadSite.right.address s) s = word)
    (previous : read_mem_bytes 8 (LoopStoreSite.output.address s) s = old) :
    ∃ fuel t, run fuel s = t ∧ LoopStable loopInnerChanged s t ∧
      MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48),
        ((LoopStoreSite.output.address s).toNat, 8)] s t ∧
      read_pc t = base + (if j + 1 = right then 952#64 else 680#64) ∧
      r (.GPR 16#5) t = BitVec.ofNat 64 (j + 1) ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (SszNative.LimbMul.step a word old carry.toNat).2 ∧
      r (.GPR 17#5) t = 0#64 ∧
      read_mem_bytes 8 (LoopStoreSite.output.address s) t =
        (SszNative.LimbMul.step a word old carry.toNat).1 := by
  have physicalCount : left + right < 2^64 := by omega
  let g := block base [.p680, .p684, .p688] s
  have guard := inner_guard_run s base left right i j code error aligned pc row column count
    physicalCount leftIndex rightIndex
  have runG : run 3 s = g := guard.1
  have gp : read_pc g = base + 692#64 := by simpa only [runG] using guard.2.1
  have gf := loop_guard_stable base s
  have gm : g.mem = s.mem := by
    simp [g, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  have gr (reg : BitVec 5) (different : reg ≠ 0#5) : r (.GPR reg) g = r (.GPR reg) s := by
    simp_all [g, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  have ga : LoopLoadSite.right.address g = LoopLoadSite.right.address s := by
    simp [LoopLoadSite.address, LoopLoadSite.pointer, gr]
  let l := loopLoaded .right g base word
  have runL : run 8 g = l := by
    apply loop_load_run .right g base word (gf.code code) (gf.error.trans error)
      (gf.aligned aligned) gp
    · rw [gf.sp]; omega
    · rw [ga]; exact sourcePhysical
    · rw [ga, gf.sp]; omega
    · rw [ga, Memory.mem_eq_iff_read_mem_bytes_eq.mp gm]; exact source
  have lf := loop_load_stable .right g base word
  have glf := gf.trans lf
  have lr (reg : BitVec 5) (different : reg ≠ 18#5) : r (.GPR reg) l = r (.GPR reg) g :=
    loop_loaded_registers .right g base word reg different
  have la : LoopLoadSite.output.address l = LoopStoreSite.output.address s := by
    simp [LoopLoadSite.address, LoopLoadSite.pointer, LoopStoreSite.address,
      LoopStoreSite.pointer, LoopStoreSite.index, lr, gr]
  have lm := loop_loaded_frame .right g base word (by rw [gf.sp]; omega)
  have oldL : read_mem_bytes 8 (LoopStoreSite.output.address s) l = old := by
    rw [lm.read _ _ outputPhysical (by
      right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rw [gf.sp]
      exact Or.elim outputSeparate (fun h => Or.inl (by omega)) Or.inr),
      Memory.mem_eq_iff_read_mem_bytes_eq.mp gm]
    exact previous
  let o := loopLoaded .output l base old
  have runO : run 8 l = o := by
    apply loop_load_run .output l base old (glf.code code) (glf.error.trans error)
      (glf.aligned aligned) (loop_loaded_pc .right g base word)
    · rw [glf.sp]; omega
    · rw [la]; exact outputPhysical
    · rw [la, glf.sp]; omega
    · rw [la]; exact oldL
  have of := loop_load_stable .output l base old
  have glof := glf.trans of
  have or (reg : BitVec 5) (different : reg ≠ 1#5) : r (.GPR reg) o = r (.GPR reg) l :=
    loop_loaded_registers .output l base old reg different
  have o18 : r (.GPR 18#5) o = word := by rw [or _ (by decide)]; exact loop_loaded_value .right g base word
  have o14 : r (.GPR 14#5) o = a := (glof.registers _ (by decide)).trans factor
  have o15 : r (.GPR 15#5) o = carry := by rw [or _ (by decide), lr _ (by decide), gr _ (by decide)]; exact incoming
  have o17 : r (.GPR 17#5) o = 0#64 := by rw [or _ (by decide), lr _ (by decide), gr _ (by decide)]; exact zero
  have o16 : r (.GPR 16#5) o = BitVec.ofNat 64 j := by rw [or _ (by decide), lr _ (by decide), gr _ (by decide)]; exact column
  let p := highProductCompleted o base
  have runP : run 29 o = p := high_product_run o base (glof.code code)
    (glof.error.trans error) (glof.aligned aligned) (loop_loaded_pc .output l base old)
  have pf := loop_product_stable o base (by rw [glof.sp]; exact stack)
  have allP := glof.trans pf
  have pr (reg : BitVec 5) (h0 : reg ≠ 0#5) (h18 : reg ≠ 18#5) :
      r (.GPR reg) p = r (.GPR reg) o := by
    rw [highProductCompleted, high_completed_registers _ base
      (by simp only [Op.effect, put, next, state_simp_rules]; rw [glof.sp]; exact stack) reg h18]
    simp [Op.effect, put, next, state_simp_rules, h0]
  have product := high_product_values o base (by rw [glof.sp]; exact stack)
  have product0 : r (.GPR 0#5) p = word * a := by simpa only [o18, o14] using product.1
  have product18 : r (.GPR 18#5) p = NatMulProduct.high word a := by simpa only [o18, o14] using product.2
  let d := loopAdds base p
  have pp : read_pc p = base + 872#64 := loop_product_pc o base (loop_loaded_pc .output l base old)
  have runD : run 4 p = d := loop_adds_run p base (allP.code code)
    (allP.error.trans error) (allP.aligned aligned) pp
  have df := loop_adds_stable base p
  have allD := allP.trans df
  have arithmetic := loop_adds_values p base word a old carry product0 product18
    (by rw [pr _ (by decide) (by decide)]; exact loop_loaded_value .output l base old)
    (by rw [pr _ (by decide) (by decide)]; exact o15)
    (by rw [pr _ (by decide) (by decide)]; exact o17)
  have commute : SszNative.LimbMul.step word a old carry.toNat =
      SszNative.LimbMul.step a word old carry.toNat := by
    simp only [SszNative.LimbMul.step, Nat.mul_comm]
  rw [commute] at arithmetic
  have d16 : r (.GPR 16#5) d = BitVec.ofNat 64 j := by
    simpa [d, loopAdds, block, Op.effect, put, next, state_simp_rules, pr] using o16
  have d0 : r (.GPR 0#5) d = BitVec.ofNat 64 (j + 1) := by
    simp [d, loopAdds, block, Op.effect, put, next, state_simp_rules, pr, o16, BitVec.ofNat_add]
  have da : LoopStoreSite.output.address d = LoopStoreSite.output.address s := by
    simp only [LoopStoreSite.address, LoopStoreSite.pointer, LoopStoreSite.index]
    rw [allD.registers 11#5 (by decide), d16, column]
  let w := loopStored .output d base
  have runW : run 8 d = w := by
    apply loop_store_run .output d base (allD.code code) (allD.error.trans error)
      (allD.aligned aligned)
    · simp [d, loopAdds, block, Op.effect, put, next, state_simp_rules, pp, BitVec.add_assoc]
    · rw [allD.sp]; omega
    · rw [da]; exact outputPhysical
    · rw [da, allD.sp]; omega
  have wf := loop_store_stable .output base d
  have allW := allD.trans wf
  let c := loopCarried base w
  have runC : run (loopCarryOps w).length w = c := loop_carry_run w base (allW.code code)
    (allW.error.trans error) (allW.aligned aligned) (loop_stored_pc .output d base)
  have cf := loop_carried_stable base w
  have allC := allW.trans cf
  let t := loopColumn base c
  have runT : run 4 c = t := loop_column_run c base (allC.code code)
    (allC.error.trans error) (allC.aligned aligned) (by simp [c, loopCarried, state_simp_rules])
  have tf := loop_column_stable base c
  have allT := allC.trans tf
  have finalMemory : t.mem = w.mem := by
    simp [t, c, loopColumn, loopCarried, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]
  have c0 : r (.GPR 0#5) c = BitVec.ofNat 64 (j + 1) := by
    simpa [c, loopCarried, state_simp_rules, loop_stored_registers] using d0
  have c25 : r (.GPR 25#5) c = BitVec.ofNat 64 right := (allC.registers _ (by decide)).trans width
  have comparison : BitVec.ofNat 64 right = BitVec.ofNat 64 (j + 1) ↔ j + 1 = right := by bv_omega
  refine ⟨3 + 8 + 8 + 29 + 4 + 8 + (loopCarryOps w).length + 4, t, ?_, allT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_plus, run_plus, run_plus, run_plus, run_plus, run_plus, run_plus,
      runG, runL, runO, runP, runD, runW, runC, runT]
  · intro address outside
    have stackOut := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
    have wordOut := outside ((LoopStoreSite.output.address s).toNat, 8) (by simp)
    have wm := loop_stored_frame .output d base (by rw [allD.sp]; omega) (by rw [da]; exact outputPhysical)
    have pm := loop_product_frame o base (by rw [glof.sp]; exact stack)
    have om := loop_loaded_frame .output l base old (by rw [glf.sp]; omega)
    have dm : d.mem = p.mem := by simp [d, loopAdds, block, Op.effect, put, next, state_simp_rules]
    rw [finalMemory]
    calc
      w.mem address = d.mem address := wm address (by
        intro span member
        simp only [List.mem_cons, List.mem_singleton] at member
        rcases member with rfl | rfl
        · rw [allD.sp]; omega
        · rw [da]; exact wordOut)
      _ = p.mem address := congrFun dm address
      _ = o.mem address := pm address (by simpa only [glof.sp] using fun span member => by
        simp only [List.mem_singleton] at member; subst span; exact stackOut)
      _ = l.mem address := om address (by
        intro span member; simp only [List.mem_singleton] at member; subst span; rw [glf.sp]; omega)
      _ = g.mem address := lm address (by
        intro span member; simp only [List.mem_singleton] at member; subst span; rw [gf.sp]; omega)
      _ = s.mem address := congrFun gm address
  · rw [loop_column_pc, c0, c25, comparison]
  · simp [t, loopColumn, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, c0]
  · have carryNat : (r (.GPR 15#5) t).toNat = (SszNative.LimbMul.step a word old carry.toNat).2 := by
      simpa [t, c, loopColumn, loopCarried, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, loop_stored_registers, loop_stored_flags] using arithmetic.2
    rw [← carryNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp [t, loopColumn, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp finalMemory, ← da,
      loop_stored_word .output d base (by rw [da]; exact outputPhysical)]
    exact arithmetic.1

end SszArm.NatMul
