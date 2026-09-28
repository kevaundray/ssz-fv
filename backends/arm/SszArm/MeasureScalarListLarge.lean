import SszArm.MeasureScalarListCount

namespace SszArm.Measure.Scalar.Bytes

open Result SszNative SszNative.Limbs

theorem list_large_width (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2332#64) (physical : size < 2^64)
    (ptr : r (.GPR 8#5) s = pointer) (count : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size)
    (significant : r (.GPR 11#5) s = BitVec.ofNat 64 (sigWords words))
    (marker : r (.GPR 10#5) s = if size = 0 then 0#64 else 1#64)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base (.large pointer words) size := by
  have physicalCount : words.length < 2^64 := by have := source.2.1; omega
  have significantBound := sigWords_le_length words
  have bounded : sigWords words < 2^64 := by omega
  let wanted : Nat := if size = 0 then 0 else 1
  have marker' : r (.GPR 10#5) s = BitVec.ofNat 64 wanted := by
    by_cases zero : size = 0 <;> simpa [wanted, zero] using marker
  have wantedBound : wanted < 2^64 := by dsimp [wanted]; split <;> decide
  have equal : r (.GPR 11#5) s = r (.GPR 10#5) s ↔ sigWords words = wanted := by
    rw [significant, marker']; bv_omega
  have less : (r (.GPR 11#5) s).toNat < (r (.GPR 10#5) s).toNat ↔ sigWords words < wanted := by
    simp [significant, marker', BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
      Nat.mod_eq_of_lt wantedBound]
  let u := listWidthCompared s base
  let steps := (listWidthOps (r (.GPR 11#5) s) (r (.GPR 10#5) s)).length
  have hu : run steps s = u := list_width_run s base code error pc
  have uf : NatNarrow.Frame s u := list_width_frame s base
  have keep (reg : BitVec 5) (different : reg ≠ 10#5) : r (.GPR reg) u = r (.GPR reg) s := by
    simp [u, listWidthCompared, NatExact.r_gpr_w, different, state_simp_rules]
  have upp : r (.GPR 8#5) u = pointer := (keep _ (by decide)).trans ptr
  have upc : r (.GPR 9#5) u = BitVec.ofNat 64 words.length := (keep _ (by decide)).trans count
  have ua : r (.GPR 20#5) u = BitVec.ofNat 64 size := (keep _ (by decide)).trans actual
  by_cases same : sigWords words = wanted
  · have up : read_pc u = base + 2356#64 := by
      simp [u, listWidthCompared, equal.mpr same, state_simp_rules]
    by_cases zero : size = 0
    · obtain ⟨fuel, t, ht, tf, ready⟩ := list_zero u base (.large pointer words)
        (code.congr uf.program) (uf.error.trans error) up (by simpa [zero] using ua)
      exact ⟨steps + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf,
        by simpa [zero] using ready⟩
    · have one : sigWords words = 1 := by simpa [wanted, zero] using same
      have nonempty : 0 < words.length := by omega
      have countNonzero : (NatOperand.large pointer words).payload ≠ 0#64 := by
        change BitVec.ofNat 64 words.length ≠ 0#64
        bv_omega
      have memory := uf.words pointer words source stored
      have first : read_mem_bytes 8 pointer u = words[0]?.getD 0#64 := by
        simpa [List.getElem?_eq_getElem nonempty] using memory ⟨0, nonempty⟩
      have bound : (read_mem_bytes 8 (NatOperand.large pointer words).pointer u).toNat =
          (NatOperand.large pointer words).value := by
        rw [NatOperand.pointer, first, large_one_value pointer words (by omega)]
      obtain ⟨fuel, t, ht, tf, ready⟩ := list_word u base (.large pointer words) size
        (code.congr uf.program) (uf.error.trans error) up physical (by omega)
        upp upc ua countNonzero bound
      exact ⟨steps + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩
  · have up : read_pc u = base + 2388#64 := by
      have different : r (.GPR 11#5) s ≠ r (.GPR 10#5) s := fun h => same (equal.mp h)
      simp [u, listWidthCompared, different, state_simp_rules]
    have selected := width_selection pointer words size physical same
    have selection : (r (.GPR 10#5) u).setWidth 32 = 0#32 ↔
        size ≤ (NatOperand.large pointer words).value := by
      by_cases below : sigWords words < wanted
      · have actualBelow := less.mpr below
        simpa [u, listWidthCompared, state_simp_rules, actualBelow, below, wanted] using selected
      · have actualNotBelow : ¬(r (.GPR 11#5) s).toNat < (r (.GPR 10#5) s).toNat :=
          fun h => below (less.mp h)
        simpa [u, listWidthCompared, state_simp_rules, actualNotBelow, below, wanted] using selected
    obtain ⟨fuel, t, ht, tf, ready⟩ := list_marker u base (.large pointer words) size
      (code.congr uf.program) (uf.error.trans error) up upp upc ua selection
    exact ⟨steps + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩

end SszArm.Measure.Scalar.Bytes
