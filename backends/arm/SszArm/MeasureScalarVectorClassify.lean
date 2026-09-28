import SszArm.MeasureScalarVectorSmall
import SszArm.MeasureScalarVectorLoadNonempty

namespace SszArm.Measure.Scalar.Bytes

open Result SszNative SszNative.Limbs

def vectorWidthOps (count : Nat) : List Op :=
  [p1232, p1236, p1240] ++ if count ≤ 2 then [] else [p1244]

private theorem width1232_effect (s : ArmState) :
    p1232.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) (r (.GPR 10#5) s + 1#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 10, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem width1236_effect (s : ArmState) :
    p1236.effect s = write_pstate (AddWithCarry (r (.GPR 10#5) s) (~~~3#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 10, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem width1240_effect (s : ArmState) :
    p1240.effect s = w .PC
      (if r (.FLAG .C) s = 1#1 then r .PC s + 4#64 else r .PC s + 1616#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 404, o0 := 0, cond := 3 })) s = _
  have choices : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

private theorem width1244_effect (s : ArmState) : p1244.effect s = w .PC (r .PC s + 2508#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 627 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

macro "measure_vector_width_expand" fits:term:max : tactic => `(tactic|
  (simp only [vectorWidthOps, ($fits), ↓reduceIte]
   all_goals simp_all (config := {decide := true, instances := true})
    [Follows, effect, width1232_effect, width1236_effect, width1240_effect, width1244_effect,
     show p1232.offset = 1232 from rfl, show p1236.offset = 1236 from rfl,
     show p1240.offset = 1240 from rfl, show p1244.offset = 1244 from rfl,
     state_simp_rules, NatExact.r_gpr_w, BitVec.add_assoc]
   all_goals first | omega | (split <;> simp_all [BitVec.add_assoc] <;> omega)))

theorem vector_classify (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 (if sigWords words = 0 then 2852 else 1232))
    (physical : size < 2^64)
    (ptr : r (.GPR 8#5) s = pointer) (count : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size)
    (remembered : sigWords words ≠ 0 → r (.GPR 10#5) s = BitVec.ofNat 64 (sigWords words - 1))
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .vector t base (.large pointer words) size := by
  by_cases zero : sigWords words = 0
  · exact vector_borrowed s base pointer words size code error (by simpa [zero] using pc)
      physical ptr count actual source stored (by change sigWords words ≤ 2; omega)
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have significantBound := sigWords_le_length words
  have countBound : sigWords words < 2^64 := by omega
  have index := remembered zero
  have increment : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
      BitVec.ofNat 64 (sigWords words) := by bv_omega
  have carry : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~3#64) 1#1).2.c = 1#1 ↔
      3 ≤ sigWords words := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
  change (AddWithCarry (BitVec.ofNat 64 (sigWords words)) 18446744073709551612#64 1#1).2.c = 1#1 ↔
    3 ≤ sigWords words at carry
  let ops := vectorWidthOps (sigWords words)
  let u := effect ops s
  have hpc : r .PC s = base + 1232#64 := by simpa [read_pc, zero] using pc
  have herr : r .ERR s = .None := error
  have follows : Follows base ops s := by
    dsimp [ops]
    by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
  have hu : run ops.length s = u := runs ops s base code follows
  have uf : NatNarrow.Frame s u := by
    constructor
    · dsimp [u, ops]; by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
    · dsimp [u, ops]; by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
    · intro reg outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      dsimp [u, ops]
      by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
    · intro reg; dsimp [u, ops]
      by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
    · intro address outside; dsimp [u, ops]
      by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
  have keep (reg : BitVec 5) (member : reg ∈ [8#5, 9#5]) : r (.GPR reg) u = r (.GPR reg) s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> dsimp [u, ops] <;>
      by_cases fits : sigWords words ≤ 2 <;> measure_vector_width_expand fits
  by_cases fits : sigWords words ≤ 2
  · have up : read_pc u = base + 2856#64 := by
      dsimp [u, ops]; measure_vector_width_expand fits
    obtain ⟨fuel, t, ht, tf, ready⟩ := vector_borrowed_nonempty u base pointer words size
      (code.congr uf.program) (uf.error.trans error) up physical
      ((keep _ (by decide)).trans ptr) ((keep _ (by decide)).trans count)
      ((uf.registers _ (by decide)).trans actual)
      (uf.source _ _ source) (uf.words _ _ source stored) (by omega) fits
    exact ⟨ops.length + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩
  · have different : (NatOperand.large pointer words).value ≠ size := by
      have unequal := width_many_ne words (BitVec.ofNat 64 size) (by omega)
      simpa [NatOperand.value, NatOperand.words, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using unequal
    refine ⟨ops.length, u, hu, Frame.of_narrow uf, ?_⟩
    refine ⟨(uf.registers _ (by decide)).trans actual, ?_⟩
    simp only [Ready, Kind.accepts] at different ⊢
    rw [if_neg different]
    refine ⟨?_, (keep _ (by decide)).trans ptr, (keep _ (by decide)).trans count⟩
    dsimp [u, ops, Kind.reject]; measure_vector_width_expand fits

end SszArm.Measure.Scalar.Bytes
