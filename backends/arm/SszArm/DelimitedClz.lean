import SszArm.DelimitedBlocks
import SszArm.DelimitedArithmetic
import SszArm.UintWidthMemory

namespace SszArm.Delimited

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem shift_add (x : BitVec 32) (a b : Nat) :
    (x >>> a) >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp [Nat.add_comm, Nat.add_left_comm]

private theorem clz_iteration_frame (s : ArmState) (base : BitVec 64) :
    WidthFrame s (block base clzIterationOps s) := by
  constructor
  · exact block_program _ _ _
  · exact block_error _ _ _
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all)
      [block, clzIterationOps, Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [block, clzIterationOps, Op.effect, put, next, state_simp_rules]
  · intro a ha
    simp [block, clzIterationOps, Op.effect, put, next, state_simp_rules]

/-- The actual SUB/LSR/CBNZ loop, with arbitrary initial counter bits. The two
shift premises describe the mathematical loop bound; clz_byte_facts discharges
them for every nonzero input byte. -/
theorem clz_loop (base : BitVec 64) :
    ∀ n (s : ArmState), CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = (if n = 0 then base + 116#64 else base + 104#64) →
      (∀ i < n, (r (.GPR 9#5) s).setWidth 32 >>> i ≠ 0#32) →
      (r (.GPR 9#5) s).setWidth 32 >>> n = 0#32 →
      ∃ t, run (3 * n) s = t ∧ WidthFrame s t ∧ t.mem = s.mem ∧
        read_pc t = base + 116#64 ∧
        (r (.GPR 9#5) t).setWidth 32 = 0#32 ∧
        (r (.GPR 10#5) t).setWidth 32 =
          (r (.GPR 10#5) s).setWidth 32 - BitVec.ofNat 32 n := by
  intro n
  induction n with
  | zero =>
    intro s hc he ha hp hn hz
    refine ⟨s, rfl, WidthFrame.refl s, rfl, ?_, ?_, ?_⟩
    · simpa using hp
    · simpa using hz
    · simp
  | succ n ih =>
    intro s hc he ha hp hn hz
    let u := block base clzIterationOps s
    have hu : run 3 s = u := clzIteration_run s base hc he ha (by simpa using hp)
    have hf : WidthFrame s u := clz_iteration_frame s base
    have memory : u.mem = s.mem := by
      simp [u, block, clzIterationOps, Op.effect, put, next, state_simp_rules]
    have shift :
        (((r (.GPR 9#5) s).setWidth 32).setWidth 64 >>> 1).setWidth 32 =
          (r (.GPR 9#5) s).setWidth 32 >>> 1 := by
      rw [← BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    have h9 : (r (.GPR 9#5) u).setWidth 32 = (r (.GPR 9#5) s).setWidth 32 >>> 1 := by
      simp [u, block, clzIterationOps, Op.effect, put, next, state_simp_rules, shift]
    have h10 : (r (.GPR 10#5) u).setWidth 32 = (r (.GPR 10#5) s).setWidth 32 - 1#32 := by
      simp [u, block, clzIterationOps, Op.effect, put, next, state_simp_rules]
    have hp' : read_pc u = if n = 0 then base + 116#64 else base + 104#64 := by
      by_cases zero : n = 0
      · subst n
        simp only [Nat.zero_add] at hz
        simp [u, block, clzIterationOps, Op.effect, put, next, state_simp_rules, shift, hz]
      · have nz := hn 1 (by omega)
        simp [u, block, clzIterationOps, Op.effect, put, next, state_simp_rules, shift, zero, nz]
    have hn' : ∀ i < n, (r (.GPR 9#5) u).setWidth 32 >>> i ≠ 0#32 := by
      intro i hi
      rw [h9, shift_add]
      exact hn (1 + i) (by omega)
    have hz' : (r (.GPR 9#5) u).setWidth 32 >>> n = 0#32 := by
      rw [h9, shift_add, Nat.add_comm 1 n]
      exact hz
    obtain ⟨t, ht, htf, hmem, htp, ht9, ht10⟩ := ih u
      (by simpa only [CodeAt, hf.program] using hc) (hf.error.trans he)
      (hf.aligned ha) hp' hn' hz'
    refine ⟨t, ?_, hf.trans htf, hmem.trans memory, htp, ht9, ?_⟩
    · rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_plus, hu, ht]
    · rw [ht10, h10]
      bv_omega

/-- Byte-specific loop exit: W10 is exactly 7-highestBit, with the original
program, error field, SP, callee-saved registers and SIMD registers preserved. -/
theorem clz_byte (s : ArmState) (base : BitVec 64) (byte : UInt8)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 104#64) (nonzero : byte ≠ 0)
    (h9 : (r (.GPR 9#5) s).setWidth 32 = clzInput byte)
    (h10 : (r (.GPR 10#5) s).setWidth 32 = 32#32) :
    ∃ t, run (3 * (25 + Ssz.highestBit byte)) s = t ∧ WidthFrame s t ∧
      t.mem = s.mem ∧ read_pc t = base + 116#64 ∧
      (r (.GPR 10#5) t).setWidth 32 = BitVec.ofNat 32 (7 - Ssz.highestBit byte) := by
  obtain ⟨bound, zero, before⟩ := clz_byte_facts byte nonzero
  obtain ⟨t, ht, hf, hmem, hpc, _, hcounter⟩ := clz_loop base (25 + Ssz.highestBit byte) s
    hc he ha (by simpa using hp)
    (by intro i hi; rw [h9]; exact before ⟨i, by omega⟩ hi)
    (by simpa only [h9] using zero)
  refine ⟨t, ht, hf, hmem, hpc, ?_⟩
  rw [hcounter, h10]
  have bit := SszNative.BitView.highestBit_lt byte
  bv_omega

end SszArm.Delimited
