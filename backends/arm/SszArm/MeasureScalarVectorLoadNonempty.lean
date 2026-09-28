import SszArm.MeasureScalarVectorLoad

namespace SszArm.Measure.Scalar.Bytes

open Result SszNative

def vectorNonemptyLoadOps (count : Nat) : List Op :=
  [p2856, p2860, p2864] ++ if count < 2 then [p3004, p3008] else [p2868, p2872]

macro "measure_vector_nonempty_expand" short:term:max : tactic => `(tactic|
  (simp only [vectorNonemptyLoadOps, ($short), ↓reduceIte]
   all_goals simp_all (config := {decide := true, instances := true})
    [Follows, effect, VectorLoadSteps.load2856_effect, VectorLoadSteps.load2860_effect,
     VectorLoadSteps.load2864_effect, VectorLoadSteps.load2868_effect, VectorLoadSteps.load2872_effect,
     VectorLoadSteps.load3004_effect, VectorLoadSteps.load3008_effect,
     show p2856.offset = 2856 from rfl, show p2860.offset = 2860 from rfl,
     show p2864.offset = 2864 from rfl, show p2868.offset = 2868 from rfl,
     show p2872.offset = 2872 from rfl, show p3004.offset = 3004 from rfl,
     show p3008.offset = 3008 from rfl,
     state_simp_rules, NatExact.r_gpr_w, BitVec.add_assoc]
   all_goals (split <;> simp_all [BitVec.add_assoc] <;> omega)))

/-- The width classifier reaches the original load at 2856, bypassing the
zero-count branch at 2852 because the scan already established a nonzero cap. -/
theorem vector_borrowed_nonempty (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2856#64) (physical : size < 2^64)
    (ptr : r (.GPR 8#5) s = pointer)
    (count : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words)
    (nonempty : 0 < words.length) (fits : (NatOperand.large pointer words).wordCount ≤ 2) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .vector t base (.large pointer words) size := by
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have carry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  have first : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
    simpa [List.getElem?_eq_getElem nonempty] using stored ⟨0, nonempty⟩
  have second : 2 ≤ words.length → read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0#64 := by
    intro enough
    have inside : 1 < words.length := by omega
    simpa [List.getElem?_eq_getElem inside] using stored ⟨1, inside⟩
  let ops := vectorNonemptyLoadOps words.length
  let u := effect ops s
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base ops s := by
    dsimp only [ops]
    by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
  have hu : run ops.length s = u := runs ops s base code follows
  have uf : NatNarrow.Frame s u := by
    constructor
    · dsimp [u, ops]; by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
    · dsimp [u, ops]; by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
    · intro reg outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      dsimp [u, ops]; by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
    · intro reg; dsimp [u, ops]
      by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
    · intro address outside; dsimp [u, ops]
      by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
  have up : read_pc u = base + 3732#64 := by
    dsimp [u, ops]; by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
  have keep (reg : BitVec 5) (member : reg ∈ [8#5, 9#5]) : r (.GPR reg) u = r (.GPR reg) s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> dsimp [u, ops] <;>
      by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
  have low : r (.GPR 10#5) u = words[0]?.getD 0#64 := by
    dsimp [u, ops]; by_cases short : words.length < 2 <;> measure_vector_nonempty_expand short
  have high : r (.GPR 11#5) u = words[1]?.getD 0#64 := by
    by_cases short : words.length < 2
    · have absent : words[1]? = none := List.getElem?_eq_none (by omega)
      dsimp [u, ops]; measure_vector_nonempty_expand short
    · have loaded := second (by omega)
      dsimp [u, ops]; measure_vector_nonempty_expand short
  obtain ⟨fuel, t, ht, tf, ready⟩ := vector_finish u base (.large pointer words) size
    (code.congr uf.program) (uf.error.trans error) up physical
    ((keep _ (by decide)).trans ptr) ((keep _ (by decide)).trans count)
    ((uf.registers _ (by decide)).trans actual) fits low high
  exact ⟨ops.length + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩

end SszArm.Measure.Scalar.Bytes
