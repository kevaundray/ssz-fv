import SszArm.NatDivisionArenaChecks
import SszArm.NatCompareMemory
import SszArm.DelimitedMemory

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def arenaLayoutLimitOps : List Op := [.p168, .p172]
def arenaLayoutBytes (s : ArmState) : BitVec 64 := r (.GPR 8#5) s <<< 3

def arenaLayoutSpill (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 10#5) s) s

def arenaLayoutOps (s : ArmState) : List Op :=
  [.p176, .p180, .p184, .p188, .p192] ++
    if arenaLayoutBytes s &&& 9223372036854775808#64 = 0#64
    then [.p196, .p200, .p204] else [.p208, .p212, .p216]

theorem arena_layout_limit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 168#64) :
    run 2 s = block base arenaLayoutLimitOps s := by
  apply block_run base arenaLayoutLimitOps s hc he ha
  have hpc : r .PC s = base + 168#64 := hp
  simp [arenaLayoutLimitOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem arena_layout_limit_effect (s : ArmState) (base : BitVec 64) :
    let t := block base arenaLayoutLimitOps s
    read_pc t = (if 2^61 ≤ (r (.GPR 8#5) s).toNat
      then base + 812#64 else base + 176#64) ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ t.mem = s.mem ∧ ArenaFrame s t := by
  have shift : (r (.GPR 8#5) s >>> 61 ≠ 0#64) ↔
      2^61 ≤ (r (.GPR 8#5) s).toNat := by bv_omega
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases bound : 2^61 ≤ (r (.GPR 8#5) s).toNat
    · have nonzero := shift.mpr bound
      simp [arenaLayoutLimitOps, block, Op.effect, put, next, state_simp_rules, nonzero, bound]
    · have zero : r (.GPR 8#5) s >>> 61 = 0#64 := by
        by_cases zero : r (.GPR 8#5) s >>> 61 = 0#64
        · exact zero
        · exact False.elim (bound (shift.mp zero))
      simp [arenaLayoutLimitOps, block, Op.effect, put, next, state_simp_rules, zero, bound]
  · simp [arenaLayoutLimitOps, block, Op.effect, put, next, state_simp_rules]
  · simp [arenaLayoutLimitOps, block, Op.effect, put, next, state_simp_rules]
  · refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [arenaLayoutLimitOps, block, Op.effect, put, next,
        state_simp_rules]
    · intro reg
      simp [arenaLayoutLimitOps, block, Op.effect, put, next, state_simp_rules]

theorem arena_layout_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 176#64) :
    run 8 s = block base (arenaLayoutOps s) s := by
  have length : (arenaLayoutOps s).length = 8 := by
    unfold arenaLayoutOps
    split <;> rfl
  rw [← length]
  apply block_run base (arenaLayoutOps s) s hc he ha
  have hpc : r .PC s = base + 176#64 := hp
  unfold arenaLayoutOps
  split <;>
    simp_all [arenaLayoutBytes, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

/-- Both exits restore the lowered spill and leave the arena untouched. -/
theorem arena_layout_effect (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    let t := block base (arenaLayoutOps s) s
    read_pc t = (if (arenaLayoutBytes s).toNat < 2^63
      then base + 220#64 else base + 812#64) ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = arenaLayoutBytes s ∧
      r (.GPR 10#5) t = r (.GPR 10#5) s ∧
      t.mem = (arenaLayoutSpill s).mem ∧ ArenaFrame s t := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (arenaLayoutSpill s) =
      r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  simp only [arenaLayoutSpill] at restore
  have high := SszNative.Arena.high_bit_clear (arenaLayoutBytes s)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try
    solve
    | (unfold arenaLayoutOps; split <;>
        simp_all [arenaLayoutBytes, arenaLayoutSpill, block, Op.effect, put, next,
          state_simp_rules, NatCompare.read_spill_w, NatCompare.spill_mem_w,
          BitVec.sub_add_cancel, BitVec.add_assoc])
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases hsp : reg = 31#5
    · subst reg
      unfold arenaLayoutOps
      split <;> simp [block, Op.effect, put, next, state_simp_rules, BitVec.sub_add_cancel]
    · unfold arenaLayoutOps
      split <;> simp_all [block, Op.effect, put, next, state_simp_rules]
  · intro reg
    unfold arenaLayoutOps
    split <;> simp [block, Op.effect, put, next, state_simp_rules]

theorem arena_layout_memory (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)]
      s (block base (arenaLayoutOps s) s) := by
  intro a outside
  rw [(arena_layout_effect s base hs).2.2.2.2.1]
  have h := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ a (by bv_omega) (by bv_omega)

theorem arena_layout_bytes (s : ArmState)
    (bound : (r (.GPR 8#5) s).toNat < 2^61) :
    (arenaLayoutBytes s).toNat = 8 * (r (.GPR 8#5) s).toNat := by
  simp only [arenaLayoutBytes, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- Executes both the multiplication overflow guard and the signed-size guard. -/
theorem arena_layout_checks_runs (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 168#64) (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ ArenaFrame s t ∧
      Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      ((¬ 8 * (r (.GPR 8#5) s).toNat < 2^63 ∧ read_pc t = base + 812#64) ∨
        (8 * (r (.GPR 8#5) s).toNat < 2^63 ∧ read_pc t = base + 220#64 ∧
          (r (.GPR 9#5) t).toNat = 8 * (r (.GPR 8#5) s).toNat)) := by
  let u := block base arenaLayoutLimitOps s
  have hu := arena_layout_limit_run s base hc he ha hp
  have eu := arena_layout_limit_effect s base
  by_cases limit : (r (.GPR 8#5) s).toNat < 2^61
  · have upc : read_pc u = base + 176#64 := eu.1.trans (if_neg (by omega))
    have us : 16 ≤ (r (.GPR 31#5) u).toNat := by rw [eu.2.2.2.sp]; exact hs
    let t := block base (arenaLayoutOps u) u
    have ht := arena_layout_run u base (eu.2.2.2.code base hc)
      (eu.2.2.2.error.trans he) (eu.2.2.2.aligned ha) upc
    have et := arena_layout_effect u base us
    have bytes : (arenaLayoutBytes u).toNat = 8 * (r (.GPR 8#5) s).toNat := by
      rw [arena_layout_bytes u (by rw [eu.2.1]; exact limit), eu.2.1]
    refine ⟨2 + 8, t, ?_, eu.2.2.2.trans et.2.2.2.2.2, ?_,
      et.2.1.trans eu.2.1, ?_⟩
    · rw [run_plus, hu, ht]
    · intro a outside
      rw [← eu.2.2.1]
      have usp : r (.GPR 31#5) u = r (.GPR 31#5) s := eu.2.2.2.sp
      exact arena_layout_memory u base us a (by simpa only [usp] using outside)
    · by_cases layout : 8 * (r (.GPR 8#5) s).toNat < 2^63
      · exact Or.inr ⟨layout, et.1.trans (if_pos (by rw [bytes]; exact layout)),
          (congrArg BitVec.toNat et.2.2.1).trans bytes⟩
      · exact Or.inl ⟨layout, et.1.trans (if_neg (by rw [bytes]; exact layout))⟩
  · refine ⟨2, u, hu, eu.2.2.2, ?_, eu.2.1, Or.inl ⟨by omega, ?_⟩⟩
    · intro a outside
      rw [eu.2.2.1]
    · exact eu.1.trans (if_pos (by omega))

end SszArm.NatDivision
