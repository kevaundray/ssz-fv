import SszArm.MeasureScalarVectorLoad

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

@[irreducible] def vectorSmallReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3732#64)
    (w (.GPR 10#5) (r (.GPR 9#5) s) (w (.GPR 11#5) 0#64 s))

theorem vector_small_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2316#64) : run 3 s = vectorSmallReady s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p2316, p2320, p2324] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p2316, p2320, p2324, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 3 = [p2316, p2320, p2324].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p2316, p2320, p2324, Op.effect, exec_inst, vectorSmallReady,
     state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc,
     NatExact.gpr_w_pc, w_of_w_shadow]

theorem vector_small_frame (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (vectorSmallReady s base) := by
  constructor
  · simp [vectorSmallReady, state_simp_rules]
  · simp [vectorSmallReady, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [vectorSmallReady, state_simp_rules]
  · intro reg; simp [vectorSmallReady, state_simp_rules]
  · intro address outside; simp [vectorSmallReady, state_simp_rules]

theorem vector_small (s : ArmState) (base word : BitVec 64) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2316#64) (physical : size < 2^64)
    (pointer : r (.GPR 8#5) s = 0#64) (payload : r (.GPR 9#5) s = word)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .vector t base (.small word) size := by
  let u := vectorSmallReady s base
  have hu : run 3 s = u := vector_small_run s base code error pc
  have uf : NatNarrow.Frame s u := vector_small_frame s base
  have fits : (NatOperand.small word).wordCount ≤ 2 := by
    have bound := SszNative.Limbs.sigWords_le_length [word]
    change SszNative.Limbs.sigWords [word] ≤ 2
    simp only [List.length_cons, List.length_nil] at bound
    omega
  obtain ⟨fuel, t, ht, tf, ready⟩ := vector_finish u base (.small word) size
    (code.congr uf.program) (uf.error.trans error)
    (by simp [u, vectorSmallReady, state_simp_rules]) physical
    (by simpa (config := {decide := true}) [u, vectorSmallReady, state_simp_rules,
      NatOperand.pointer] using pointer)
    (by simpa (config := {decide := true}) [u, vectorSmallReady, state_simp_rules,
      NatOperand.payload] using payload)
    ((uf.registers _ (by decide)).trans actual) fits
    (by simp [u, vectorSmallReady, state_simp_rules, NatOperand.words, payload])
    (by simp [u, vectorSmallReady, state_simp_rules, NatOperand.words])
  exact ⟨3 + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩

end SszArm.Measure.Scalar.Bytes
