import SszArm.NatDivisionLoopInvariant

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

structure LoopPost (s t : ArmState) (base divisor : BitVec 64)
    (words : List (BitVec 64)) (remainder : Nat) : Prop where
  frame : LoopFrame (loopWrites (r (.GPR 31#5) s) (r (.GPR 24#5) s) words.length) s t
  written : LoopWords t (r (.GPR 24#5) s) (SszNative.LimbDivision.loop divisor words remainder).1
  remainder : (r (.GPR 1#5) t).toNat = (SszNative.LimbDivision.loop divisor words remainder).2
  bound : (r (.GPR 1#5) t).toNat < divisor.toNat
  pc : read_pc t = base + 616#64
  index : r (.GPR 23#5) t = -8#64

/-- Finite execution of the real reverse loop, including every runtime call,
for arbitrary nonempty full-width limbs and an arbitrary bounded incoming
remainder. The output retains all quotient positions prior to normalization. -/
theorem loop_run (words : List (BitVec 64)) (s : ArmState) (base divisor : BitVec 64)
    (remainder : Nat) (nonempty : words ≠ [])
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 524#64)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) words.length)
    (memory : LoopWords s (r (.GPR 24#5) s) words)
    (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * (words.length - 1)))
    (hd : r (.GPR 20#5) s = divisor) (positive : 0 < divisor.toNat)
    (hr : (r (.GPR 1#5) s).toNat = remainder) (bound : remainder < divisor.toNat) :
    ∃ fuel t, run fuel s = t ∧ LoopPost s t base divisor words remainder := by
  induction words using loop_reverse_induction generalizing s remainder with
  | nil => exact False.elim (nonempty rfl)
  | snoc low word ih =>
    have sp : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) (low.length + 1) := by
      simpa using space
    have ix : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * low.length) := by simpa using index
    have hw : read_mem_bytes 8 (loopAddress s) s = word := by
      have h := ((LoopWords.append s _ low [word]).mp memory).2 0 (by simp)
      simpa [loopAddress, ix] using h
    let u := loopIteration s base
    have hu : run (loopIterationFuel s base) s = u :=
      loopIteration_run s base (low.length + 1) low.length hc he ha hp sp (by omega) ix
        (by simpa only [hd] using positive)
    have uf := loopIteration_full_frame s base (low.length + 1) low.length sp (by omega) ix
    have usp : r (.GPR 31#5) u = r (.GPR 31#5) s := uf.sp
    have u24 : r (.GPR 24#5) u = r (.GPR 24#5) s :=
      uf.registers _ (by decide) (by decide) (by decide) (by decide)
    have u20 : r (.GPR 20#5) u = divisor :=
      (uf.registers _ (by decide) (by decide) (by decide) (by decide)).trans hd
    have arithmetic := loopIteration_arithmetic s base divisor word remainder hd hw hr bound
    have uq : r (.GPR 0#5) u = (SszNative.LimbDivision.step divisor remainder word).1 := arithmetic.1
    have ur : (r (.GPR 1#5) u).toNat = (SszNative.LimbDivision.step divisor remainder word).2 := arithmetic.2
    have divisorNonzero : divisor ≠ 0#64 := by intro hz; simp [hz] at positive
    have nextBound := SszNative.LimbDivision.step_remainder_lt divisor word remainder divisorNonzero
    have highWord : read_mem_bytes 8 (r (.GPR 24#5) s + BitVec.ofNat 64 (8 * low.length)) u =
        (SszNative.LimbDivision.step divisor remainder word).1 := by
      have hwritten := loopIteration_word s base (low.length + 1) low.length sp (by omega) ix
      simpa only [loopAddress, ix, ← uq] using hwritten
    by_cases empty : low = []
    · subst low
      refine ⟨loopIterationFuel s base, u, hu, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using uf
      · intro i hi
        have zero : i = 0 := by simpa [SszNative.LimbDivision.loop] using hi
        subst i
        simpa [SszNative.LimbDivision.loop] using highWord
      · simpa [SszNative.LimbDivision.loop] using ur
      · rw [ur]; exact nextBound
      · simp [u, loopIteration_pc, ix]
      · simp [u, loopIteration_index, ix]
    · have lowerMemory : LoopWords u (r (.GPR 24#5) u) low := by
        rw [u24]
        exact loopIteration_lower s base low word sp ix memory
      have lowerSpace : LoopSpace (r (.GPR 31#5) u) (r (.GPR 24#5) u) low.length := by
        rw [usp, u24]
        exact sp.prefix (by omega)
      have lowerIndex : r (.GPR 23#5) u = BitVec.ofNat 64 (8 * (low.length - 1)) := by
        have lengthPositive : 0 < low.length := List.length_pos_iff.mpr empty
        have subtract : 8 * low.length = 8 * (low.length - 1) + 8 := by omega
        simp only [u, loopIteration_index, ix, subtract, BitVec.ofNat_add]
        bv_omega
      have notzero : r (.GPR 23#5) s ≠ 0#64 := by
        have lengthPositive : 0 < low.length := List.length_pos_iff.mpr empty
        have physical := sp.physical
        rw [ix]
        intro zero
        have hn := congrArg BitVec.toNat zero
        simp only [BitVec.toNat_ofNat] at hn
        rw [Nat.mod_eq_of_lt (by omega)] at hn
        omega
      have lowerPc : read_pc u = base + 524#64 := by
        simp [u, loopIteration_pc, notzero]
      have lowerCode : JointCodeAt u base := by
        simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, uf.program] using hc
      obtain ⟨fuel, t, ht, post⟩ := ih u (SszNative.LimbDivision.step divisor remainder word).2
        empty lowerCode (uf.error.trans he) (uf.aligned ha) lowerPc lowerSpace lowerMemory
        lowerIndex u20 positive ur nextBound
      have tf : LoopFrame (loopWrites (r (.GPR 31#5) s) (r (.GPR 24#5) s) low.length) u t := by
        simpa only [usp, u24] using post.frame
      have highPreserved := loopFrame_upper sp tf
      refine ⟨loopIterationFuel s base + fuel, t, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · refine ⟨?_, ?_, ?_, ?_, post.pc, post.index⟩
        · simpa using uf.trans (loopFrame_prefix tf (by omega : low.length ≤ low.length + 1))
        · simp only [SszNative.LimbDivision.loop_append, SszNative.LimbDivision.loop]
          apply (LoopWords.append t _ _ _).mpr
          constructor
          · simpa only [u24] using post.written
          · intro i hi
            have zi : i = 0 := by simpa using hi
            subst i
            simpa only [SszNative.LimbDivision.loop_length, Nat.add_zero, List.getElem_cons_zero]
              using highPreserved.trans highWord
        · simpa only [SszNative.LimbDivision.loop_append, SszNative.LimbDivision.loop] using post.remainder
        · exact post.bound

/-- Entry at MOV X1,XZR and exit through the actual branch at 616, yielding the
normalization entry at 1032. Only the structural linked-code predicate is used
for the runtime helper; no helper correctness assumption is exposed. -/
theorem divideWords_run (words : List (BitVec 64)) (s : ArmState) (base divisor : BitVec 64)
    (nonempty : words ≠ []) (hc : JointCodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 520#64)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) words.length)
    (memory : LoopWords s (r (.GPR 24#5) s) words)
    (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * (words.length - 1)))
    (hd : r (.GPR 20#5) s = divisor) (divisorBound : 2 ≤ divisor.toNat) :
    ∃ fuel t, run fuel s = t ∧
      LoopFrame (loopWrites (r (.GPR 31#5) s) (r (.GPR 24#5) s) words.length) s t ∧
      LoopWords t (r (.GPR 24#5) s) (SszNative.LimbDivision.divideWords divisor words).1 ∧
      (r (.GPR 1#5) t).toNat = (SszNative.LimbDivision.divideWords divisor words).2 ∧
      (r (.GPR 1#5) t).toNat < divisor.toNat ∧ read_pc t = base + 1032#64 := by
  let u := Op.p520.effect base s
  have first : run 1 s = u := by
    rw [run, step s base .p520 hc.1 (by simpa only [Op.row] using hp) he ha]
    rfl
  have ucode : JointCodeAt u base := by
    simpa only [u, JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, Op.program] using hc
  obtain ⟨fuel, t, ht, post⟩ := loop_run words u base divisor 0 nonempty ucode
    (by simpa only [u, Op.error] using he) (Op.aligned _ _ _ ha)
    (by simp [u, Op.effect, put, next, state_simp_rules, hp])
    (by simpa [u, Op.effect, put, next, state_simp_rules] using space)
    (by simpa [u, LoopWords, Op.effect, put, next, state_simp_rules] using memory)
    (by simpa [u, Op.effect, put, next, state_simp_rules] using index)
    (by simpa [u, Op.effect, put, next, state_simp_rules] using hd)
    (by omega) (by simp [u, Op.effect, put, next, state_simp_rules]) (by omega)
  let v := Op.p616.effect base t
  have tcode : CodeAt t base := by
    simpa only [CodeAt, post.frame.program] using ucode.1
  have last : run 1 t = v := by
    rw [run, step t base .p616 tcode (by simpa only [Op.row] using post.pc)
      (post.frame.error.trans (by simpa only [u, Op.error] using he))
      (post.frame.aligned (Op.aligned _ _ _ ha))]
    rfl
  refine ⟨1 + fuel + 1, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_plus, run_plus, first, ht, last]
  · have frame := post.frame
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [v, u, Op.effect, put, next, state_simp_rules] using frame.program
    · simpa [v, u, Op.effect, put, next, state_simp_rules] using frame.error
    · intro reg lo h21 h23 h30
      have h1 : reg ≠ 1#5 := by bv_omega
      simpa [v, u, Op.effect, put, next, state_simp_rules, h1] using frame.registers reg lo h21 h23 h30
    · intro reg
      simpa [v, u, Op.effect, put, next, state_simp_rules] using frame.sfp reg
    · simpa [v, u, loopWrites, Op.effect, put, next, state_simp_rules, MemoryFrame] using frame.memory
  · simpa [v, u, SszNative.LimbDivision.divideWords, LoopWords, Op.effect, put, next,
      state_simp_rules] using post.written
  · simpa [v, SszNative.LimbDivision.divideWords, Op.effect, state_simp_rules] using post.remainder
  · simpa [v, Op.effect, state_simp_rules] using post.bound
  · simp [v, Op.effect, state_simp_rules]

end SszArm.NatDivision
