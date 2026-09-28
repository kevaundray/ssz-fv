import SszArm.NatToU128Scan
import SszArm.NatToU128Finish

namespace SszArm.NatToU128

open UintCodec (widthLoad)
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- At pc124 the physical length, rather than significant width, decides whether
one or two original limbs are loaded. High zero padding is therefore harmless. -/
theorem large_read_ready (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (nonempty : 0 < words.length)
    (fits : sigWords words ≤ 2)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 124#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, ∃ path : FinishPath, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + BitVec.ofNat 64 path.start ∧
      SszNative.NatNarrow.toU128 (.large pointer words) = path.value t := by
  let ops : List Op := [.p124, .p128, .p132]
  let t := block base ops s
  have hpc : r .PC s = base + 124#64 := hp
  have follow : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]
  have ht : run 3 s = t := block_run base ops s hc he ha follow
  have frame : NatNarrow.Frame s t := scan_pure_frame base ops s (by decide)
  have bound : words.length < 2^64 := by have := hs.2.1; omega
  have carry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  change (AddWithCarry (BitVec.ofNat 64 words.length) 18446744073709551613#64 1#1).2.c = 1#1 ↔
    2 ≤ words.length at carry
  have low : read_mem_bytes 8 pointer s = words[0]?.getD 0 := by
    simpa [List.getElem?_eq_getElem nonempty] using hm ⟨0, nonempty⟩
  have loaded : r (.GPR 8#5) t = words[0]?.getD 0 := by
    simp [t, ops, block, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, h1, low]
  by_cases one : words.length < 2
  · refine ⟨3, t, .one, ht, frame, ?_, ?_⟩
    · simp [t, ops, block, FinishPath.start, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, h2, carry,
        show ¬ 2 ≤ words.length by omega]
    · change SszNative.NatNarrow.toU128 (.large pointer words) =
        some ((r (.GPR 8#5) t).setWidth 128)
      apply (SszNative.NatNarrow.toU128_some_iff _ _).2
      rw [loaded, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
      cases words with
      | nil => simp at nonempty
      | cons lo rest =>
        have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp at one; omega)
        subst rest
        simp [SszNative.NatOperand.value, SszNative.NatOperand.words, value]
  · have two : 2 ≤ words.length := by omega
    have high : read_mem_bytes 8 (r (.GPR 1#5) t + 8#64) t = words[1]?.getD 0 := by
      have observed := frame.words pointer words hs hm ⟨1, by omega⟩
      rw [frame.registers 1#5 (by decide), h1]
      simpa [List.getElem?_eq_getElem (by omega : 1 < words.length)] using observed
    refine ⟨3, t, .two, ht, frame, ?_, ?_⟩
    · simp [t, ops, block, FinishPath.start, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, h2, carry, two]
    · change SszNative.NatNarrow.toU128 (.large pointer words) =
        some (read_mem_bytes 8 (r (.GPR 1#5) t + 8#64) t ++ r (.GPR 8#5) t)
      apply (SszNative.NatNarrow.toU128_some_iff _ _).2
      rw [high, loaded, append_toNat]
      have size := SszNative.NatDivision.value_lt_128
        (SszNative.NatOperand.large pointer words) fits
      cases words with
      | nil => simp at two
      | cons lo rest =>
        cases rest with
        | nil => simp at two
        | cons hi rest =>
          simp only [SszNative.NatOperand.value, SszNative.NatOperand.words,
            value] at size ⊢
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          have zero : value rest = 0 := by omega
          rw [zero]
          omega

/-- Entering the significant-width loop preserves every ABI input register. -/
theorem large_entry_scan (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + BitVec.ofNat 64 (if sigWords words = 0 then 120 else 60) ∧
      (sigWords words ≠ 0 → r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words - 1)) := by
  have h1 : r (.GPR 1#5) s = pointer := owned.operandPointer
  have h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length := owned.operandPayload
  have nz : pointer ≠ 0#64 := by
    intro equal
    have positive := owned.operandAt.1
    simp [equal] at positive
  let ops : List Op := [.p0, .p4]
  let u := block base ops s
  have hpc : r .PC s = base := hp
  have follow : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, h1, nz, BitVec.add_assoc]
  have hu : run 2 s = u := block_run base ops s hc he ha follow
  have frame : NatNarrow.Frame s u := scan_pure_frame base ops s (by decide)
  have hup : read_pc u = base + 8#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1, nz, BitVec.add_assoc]
  have hu1 : r (.GPR 1#5) u = pointer := (frame.registers _ (by decide)).trans h1
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h2]
  obtain ⟨fuel, t, ht, htf, hkeep, htp, ht8⟩ := significant_scan base pointer words words.length u
    (Nat.le_refl _) (frame_code frame hc) (frame.error.trans he) (frame.aligned ha)
    hup hu1 hu9 (frame.source _ _ owned.large_source)
    (frame.words _ _ owned.large_source owned.large_words)
  refine ⟨2 + fuel, t, ?_, frame.trans htf, htp, ht8⟩
  rw [run_plus, hu, ht]

/-- Complete branch selection. The witness records the actual finite native
continuation, not an assumed execution or a normalized input representation. -/
theorem entry_ready (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (owned : Owned s operand) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base) :
    ∃ fuel t, ∃ path : FinishPath, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + BitVec.ofNat 64 path.start ∧
      SszNative.NatNarrow.toU128 operand = path.value t := by
  cases operand with
  | small scalar =>
    let t := block base [.p0] s
    have h1 : r (.GPR 1#5) s = 0#64 := owned.operandPointer
    have h2 : r (.GPR 2#5) s = scalar := owned.operandPayload
    have hpc : r .PC s = base := hp
    have ht : run 1 s = t := block_run base [.p0] s hc he ha
      (by simpa [Follows, Op.row] using hp)
    have frame : NatNarrow.Frame s t := scan_pure_frame base [.p0] s (by decide)
    refine ⟨1, t, .small, ht, frame, ?_, ?_⟩
    · simp [t, block, FinishPath.start, Op.effect, state_simp_rules, h1]
    · change SszNative.NatNarrow.toU128 (.small scalar) = some ((r (.GPR 2#5) t).setWidth 128)
      apply (SszNative.NatNarrow.toU128_some_iff _ _).2
      rw [frame.registers 2#5 (by decide), h2,
        BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
      simp [SszNative.NatOperand.value, SszNative.NatOperand.words, value]
  | large pointer words =>
    obtain ⟨fuel, u, hu, frame, hup, hu8⟩ := large_entry_scan s base pointer words owned hc he ha hp
    have h1 : r (.GPR 1#5) u = pointer :=
      (frame.registers _ (by decide)).trans owned.operandPointer
    have h2 : r (.GPR 2#5) u = BitVec.ofNat 64 words.length :=
      (frame.registers _ (by decide)).trans owned.operandPayload
    have hs := frame.source _ _ owned.large_source
    have hm := frame.words _ _ owned.large_source owned.large_words
    have hbound : words.length < 2^64 := by have := hs.2.1; omega
    have finishRead (v : ArmState) (fuel' : Nat) (hv : run fuel' u = v)
        (vf : NatNarrow.Frame u v) (vp : read_pc v = base + 124#64)
        (nonempty : 0 < words.length) (fits : sigWords words ≤ 2) :
        ∃ total t, ∃ path : FinishPath, run total s = t ∧ NatNarrow.Frame s t ∧
          read_pc t = base + BitVec.ofNat 64 path.start ∧
          SszNative.NatNarrow.toU128 (.large pointer words) = path.value t := by
      obtain ⟨rest, t, path, ht, tf, tp, result⟩ := large_read_ready v base pointer words
        nonempty fits (frame_code (frame.trans vf) hc) ((frame.trans vf).error.trans he)
        ((frame.trans vf).aligned ha) vp
        ((vf.registers _ (by decide)).trans h1) ((vf.registers _ (by decide)).trans h2)
        (vf.source _ _ hs) (vf.words _ _ hs hm)
      refine ⟨fuel + fuel' + rest, t, path, ?_, frame.trans (vf.trans tf), tp, result⟩
      rw [run_plus, run_plus, hu, hv, ht]
    by_cases zero : sigWords words = 0
    · have up : read_pc u = base + 120#64 := by simpa [zero] using hup
      let v := block base [.p120] u
      have hv : run 1 u = v := block_run base [.p120] u (frame_code frame hc)
        (frame.error.trans he) (frame.aligned ha) (by simpa [Follows, Op.row] using up)
      have vf : NatNarrow.Frame u v := scan_pure_frame base [.p120] u (by decide)
      by_cases empty : words.length = 0
      · have nil : words = [] := List.eq_nil_of_length_eq_zero empty
        refine ⟨fuel + 1, v, .small, ?_, frame.trans vf, ?_, ?_⟩
        · rw [run_plus, hu, hv]
        · simp [v, block, FinishPath.start, Op.effect, state_simp_rules, h2, empty]
        · change SszNative.NatNarrow.toU128 (.large pointer words) = some ((r (.GPR 2#5) v).setWidth 128)
          apply (SszNative.NatNarrow.toU128_some_iff _ _).2
          rw [vf.registers 2#5 (by decide), h2]
          simp [nil, SszNative.NatOperand.value, SszNative.NatOperand.words, value]
      · have countnz : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
        exact finishRead v 1 hv vf
          (by simp [v, block, Op.effect, state_simp_rules, h2, countnz])
          (by omega) (by omega)
    · have up : read_pc u = base + 60#64 := by simpa [zero] using hup
      have count := hu8 zero
      have sigbound : sigWords words < 2^64 := by have := sigWords_le_length words; omega
      have increment : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
          BitVec.ofNat 64 (sigWords words) := by bv_omega
      let ops : List Op := [.p60, .p64, .p68]
      let v := block base ops u
      have hpc : r .PC u = base + 60#64 := up
      have hv : run 3 u = v := block_run base ops u (frame_code frame hc)
        (frame.error.trans he) (frame.aligned ha)
        (by simp [ops, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
          Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc])
      have vf : NatNarrow.Frame u v := scan_pure_frame base ops u (by decide)
      have carry : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~3#64) 1#1).2.c = 1#1 ↔
          3 ≤ sigWords words := by
        rw [Udivti3.cmp_carry]
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigbound]
      change (AddWithCarry (BitVec.ofNat 64 (sigWords words)) 18446744073709551612#64 1#1).2.c = 1#1 ↔
        3 ≤ sigWords words at carry
      by_cases fits : sigWords words ≤ 2
      · exact finishRead v 3 hv vf
          (by simp [v, ops, block, Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules, count, increment, carry,
            show ¬ 3 ≤ sigWords words by omega])
          (by have := sigWords_le_length words; omega) fits
      · refine ⟨fuel + 3, v, .none, ?_, frame.trans vf, ?_, ?_⟩
        · rw [run_plus, hu, hv]
        · simp [v, ops, block, FinishPath.start, Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules, count, increment, carry,
            show 3 ≤ sigWords words by omega]
        · simp [FinishPath.value, SszNative.NatNarrow.toU128,
            SszNative.NatOperand.wordCount, SszNative.NatOperand.words, fits]

end SszArm.NatToU128
