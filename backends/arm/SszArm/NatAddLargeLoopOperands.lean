import SszArm.NatAddLargeLoopRead

namespace SszArm.NatAdd.LargeLoop

open NatCompare (Source Words Operand saved)
open Delimited (Span Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem operand_frame {writes : List Span} {s t : ArmState}
    (frame : LoopFrame writes s t) (pointer payload : BitVec 64)
    (words : List (BitVec 64)) (input : Operand s pointer payload words)
    (owned : pointer ≠ 0#64 → Protected writes pointer.toNat (8 * words.length)) :
    Operand t pointer payload words := by
  rcases input with small | ⟨nonnull, count, source, limbs⟩
  · exact Or.inl small
  · exact Or.inr ⟨nonnull, count, frame.source _ _ source,
      frame.words _ _ source limbs (owned nonnull)⟩

/-- Execute the selected right gate and either the actual eight-instruction
right load or the explicit zero-word block. Index starts after word zero. -/
theorem right_run (s : ArmState) (base : BitVec 64) (kind : GateKind)
    (right : List (BitVec 64)) (index : Nat) (writes : List Span)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hi : 1 ≤ index) (h15 : (r (.GPR 15#5) s).toNat = index)
    (h13 : r (.GPR 13#5) s = if r (.GPR 3#5) s = 0#64 then 1#64 else 0#64)
    (input : Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right)
    (owned : r (.GPR 3#5) s ≠ 0#64 →
      Protected writes (r (.GPR 3#5) s).toNat (8 * right.length))
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes) :
    ∃ fuel t, run fuel s = t ∧ LoopFrame writes s t ∧
      read_pc t = base + 1604#64 ∧ r (.GPR 17#5) t = right[index]?.getD 0 ∧
      (∀ reg : BitVec 5, reg ≠ 17#5 → r (.GPR reg) t = r (.GPR reg) s) := by
  let within := decide ((r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat)
  let small := decide (r (.GPR 3#5) s = 0#64)
  let g := gateResult s base within small
  have grun : run (gateOps kind within small).length s = g :=
    gate_run s base kind small hc he ha hp hs (by simpa [small] using h13)
  have gf : LoopFrame writes s g := gate_frame s base within small writes hs slot
  have greg : ∀ reg : BitVec 5, reg ≠ 17#5 → r (.GPR reg) g = r (.GPR reg) s := by
    intro reg hr
    simp [g, gateResult, saved, Udivti3.compare,
      Udivti3.next, state_simp_rules, hr]
  have gp : read_pc g = base + if within && !small then 1572#64 else 1860#64 := by
    simp [g, gateResult, state_simp_rules]
  by_cases load : (within && !small) = true
  · have bits : within = true ∧ small = false := by
      cases hwithin : within <;> cases hsmall : small <;>
        simp [hwithin, hsmall] at load ⊢
    have large : r (.GPR 3#5) s ≠ 0#64 := by simpa [small] using bits.2
    obtain ⟨count, source, limbs⟩ := input.large large
    have inbounds : index < right.length := by
      simpa [within, h15, count] using bits.1
    have gs := gf.source _ _ source
    have gm := gf.words _ _ source limbs (owned large)
    have g15 : r (.GPR 15#5) g = BitVec.ofNat 64 index := by
      rw [greg _ (by decide)]
      exact BitVec.eq_of_toNat_eq (by simp [← h15])
    have loadword : read_mem_bytes 8
        (r (.GPR LoadKind.loopRight.ptr) g + (r (.GPR LoadKind.loopRight.index) g <<< 3))
        (saved g LoadKind.loopRight.tmp) = right[index]?.getD 0 := by
      simp only [LoadKind.ptr, LoadKind.index, greg 3#5 (by decide), g15]
      exact NatCompare.limb_load g (r (.GPR 3#5) s) right index _ inbounds gs gm
    let t := loadResult g base .loopRight (right[index]?.getD 0)
    have trun : run 8 g = t := NatAdd.load_run g base _ .loopRight (gf.code hc)
      (gf.error.trans he) (gf.aligned ha) (by simpa [load, LoadKind.start] using gp)
      gs.1 loadword
    have tf := load_frame g base (right[index]?.getD 0) .loopRight writes gs.1
      (by simpa only [gf.sp] using slot) (by decide)
    refine ⟨(gateOps kind within small).length + 8, t, ?_, gf.trans tf, ?_, ?_, ?_⟩
    · rw [run_plus, grun, trun]
    · simp [t, loadResult, LoadKind.start, state_simp_rules]
    · simp [t, loadResult, LoadKind.dst, state_simp_rules]
    · intro reg hr
      simpa [t, loadResult, LoadKind.dst, saved, state_simp_rules, hr]
        using greg reg hr
  · have zero : right[index]?.getD 0#64 = 0#64 := by
      by_cases smallPointer : r (.GPR 3#5) s = 0#64
      · rw [input.small smallPointer, List.getElem?_eq_none (by simp; omega)]
        rfl
      · obtain ⟨count, _, _⟩ := input.large smallPointer
        have notwithin : ¬index < right.length := by
          simpa [within, small, h15, count, smallPointer] using load
        rw [List.getElem?_eq_none (by omega)]
        rfl
    have skip : (within && !small) = false := by
      cases branch : (within && !small) with
      | false => rfl
      | true => exact False.elim (load branch)
    have gp' : read_pc g = base + 1860#64 := by simpa [skip] using gp
    let t := block base [.p1860, .p1864] g
    have follows : Follows base [.p1860, .p1864] g := by
      have gpc : r .PC g = base + 1860#64 := gp'
      simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
        gpc, BitVec.add_assoc]
    have trun : run 2 g = t := block_run base _ g (gf.code hc)
      (gf.error.trans he) (gf.aligned ha) follows
    have tf := pure_frame base [.p1860, .p1864] g writes (by decide)
    refine ⟨(gateOps kind within small).length + 2, t, ?_, gf.trans tf, ?_, ?_, ?_⟩
    · rw [run_plus, grun, trun]
    · simp [t, block, Op.effect, put, next, state_simp_rules]
    · simpa [t, block, Op.effect, put, next, state_simp_rules] using zero.symm
    · intro reg hr
      simpa [t, block, Op.effect, put, next, state_simp_rules, hr]
        using greg reg hr

/-- Complete actual operand-selection slice, from PC1692 to the first ADDS at
PC1604. The original physical lengths drive unsigned loads and zero extension. -/
theorem operands_run (s : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64)) (index : Nat) (writes : List Span)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1692#64)
    (h2 : (r (.GPR 2#5) s).toNat = left.length)
    (hi : 1 ≤ index) (h15 : (r (.GPR 15#5) s).toNat = index)
    (h13 : r (.GPR 13#5) s = if r (.GPR 3#5) s = 0#64 then 1#64 else 0#64)
    (source : Source s (r (.GPR 1#5) s) left)
    (limbs : Words s (r (.GPR 1#5) s) left)
    (input : Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right)
    (owned : r (.GPR 3#5) s ≠ 0#64 →
      Protected writes (r (.GPR 3#5) s).toNat (8 * right.length))
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes) :
    ∃ fuel t, run fuel s = t ∧ LoopFrame writes s t ∧
      read_pc t = base + 1604#64 ∧
      r (.GPR 16#5) t = left[index]?.getD 0 ∧
      r (.GPR 17#5) t = right[index]?.getD 0 ∧
      (∀ reg : BitVec 5, reg ≠ 16#5 → reg ≠ 17#5 →
        r (.GPR reg) t = r (.GPR reg) s) := by
  obtain ⟨urun, uf, up, ul, ureg⟩ := left_run s base (r (.GPR 1#5) s) left index
    writes hc he ha hp rfl h2 h15 source limbs slot
  let u := leftState s base left index
  change LoopFrame writes s u at uf
  have input' : Operand u (r (.GPR 3#5) u) (r (.GPR 4#5) u) right := by
    rw [ureg 3#5 (by decide), ureg 4#5 (by decide)]
    exact operand_frame uf _ _ _ input owned
  obtain ⟨fuel, t, trun, tf, tp, tr, treg⟩ := right_run u base (leftGate left index)
    right index writes (uf.code hc) (uf.error.trans he) (uf.aligned ha) up
    (by rw [uf.sp]; exact source.1) hi (by rw [ureg _ (by decide)]; exact h15)
    (by rw [ureg 13#5 (by decide), ureg 3#5 (by decide)]; exact h13)
    input' (by rw [ureg _ (by decide)]; exact owned)
    (by simpa only [uf.sp] using slot)
  refine ⟨(if index < left.length then 10 else 3) + fuel, t, ?_, uf.trans tf,
    tp, (treg _ (by decide)).trans ul, tr, ?_⟩
  · rw [run_plus, urun, trun]
  · intro reg h16 h17
    exact (treg reg h17).trans (ureg reg h16)

end SszArm.NatAdd.LargeLoop
