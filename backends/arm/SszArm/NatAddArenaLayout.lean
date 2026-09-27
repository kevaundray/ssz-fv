import SszArm.NatAddArenaChecks
import SszArm.NatCompareMemory
import SszArm.DelimitedMemory

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def arenaLayoutLimitOps : List Op := [.p144, .p148, .p152]

def arenaLayoutBytes (s : ArmState) : BitVec 64 := (r (.GPR 8#5) s <<< 3) + 8#64

def arenaLayoutSpill (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 8#5) s <<< 3) s

def arenaLayoutOps (s : ArmState) : List Op :=
  [.p156, .p160, .p164, .p168, .p172, .p176] ++
    if arenaLayoutBytes s &&& 9223372036854775808#64 = 0#64
    then [.p180, .p184, .p188] else [.p192, .p196, .p200]

theorem arena_layout_limit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 144#64) :
    run 3 s = block base arenaLayoutLimitOps s := by
  apply block_run base arenaLayoutLimitOps s hc he ha
  have hpc : r .PC s = base + 144#64 := hp
  simp [arenaLayoutLimitOps, Follows, Op.row, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

theorem arena_layout_limit_effect (s : ArmState) (base : BitVec 64) :
    let t := block base arenaLayoutLimitOps s
    read_pc t = (if 2305843009213693950 < (r (.GPR 8#5) s).toNat
      then base + 1248#64 else base + 156#64) ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ t.mem = s.mem ∧ ArenaFrame s t := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have high := Udivti3.cmp_high (r (.GPR 8#5) s) 2305843009213693950#64
    change ((AddWithCarry (r (.GPR 8#5) s) 16140901064495857665#64 1#1).2.c = 1#1 ∧
      (AddWithCarry (r (.GPR 8#5) s) 16140901064495857665#64 1#1).2.z = 0#1) ↔
        2305843009213693950 < (r (.GPR 8#5) s).toNat at high
    simp [arenaLayoutLimitOps, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules, high]
  · simp [arenaLayoutLimitOps, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]
  · simp [arenaLayoutLimitOps, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]
  · refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [arenaLayoutLimitOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro reg
      simp [arenaLayoutLimitOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]

theorem arena_layout_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 156#64) :
    run 9 s = block base (arenaLayoutOps s) s := by
  have length : (arenaLayoutOps s).length = 9 := by
    unfold arenaLayoutOps
    split <;> rfl
  rw [← length]
  apply block_run base (arenaLayoutOps s) s hc he ha
  have hpc : r .PC s = base + 156#64 := hp
  unfold arenaLayoutOps
  split <;>
    simp_all [arenaLayoutBytes, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, BitVec.add_assoc]

/-- The isize check performs a real save and reload of X9 and restores SP on both exits. -/
theorem arena_layout_effect (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    let t := block base (arenaLayoutOps s) s
    read_pc t = (if (arenaLayoutBytes s).toNat < 2^63
      then base + 204#64 else base + 1248#64) ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = r (.GPR 8#5) s <<< 3 ∧
      r (.GPR 11#5) t = arenaLayoutBytes s ∧
      t.mem = (arenaLayoutSpill s).mem ∧ ArenaFrame s t := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (arenaLayoutSpill s) =
      r (.GPR 8#5) s <<< 3 :=
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
      split <;>
        simp_all [block, Op.effect, put, next, state_simp_rules]
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
    (bound : (r (.GPR 8#5) s).toNat ≤ 2305843009213693950) :
    (arenaLayoutBytes s).toNat = 8 * ((r (.GPR 8#5) s).toNat + 1) := by
  simp only [arenaLayoutBytes, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- Both layout failure guards are executed; neither makes a cursor commitment. -/
theorem arena_layout_checks_runs (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 144#64) (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ ArenaFrame s t ∧
      Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      ((¬ 8 * ((r (.GPR 8#5) s).toNat + 1) < 2^63 ∧ read_pc t = base + 1248#64) ∨
        (8 * ((r (.GPR 8#5) s).toNat + 1) < 2^63 ∧ read_pc t = base + 204#64 ∧
          (r (.GPR 11#5) t).toNat = 8 * ((r (.GPR 8#5) s).toNat + 1))) := by
  let u := block base arenaLayoutLimitOps s
  have hu := arena_layout_limit_run s base hc he ha hp
  have eu := arena_layout_limit_effect s base
  by_cases limit : (r (.GPR 8#5) s).toNat ≤ 2305843009213693950
  · have upc : read_pc u = base + 156#64 := eu.1.trans (if_neg (by omega))
    have usp : r (.GPR 31#5) u = r (.GPR 31#5) s := eu.2.2.2.sp
    have us : 16 ≤ (r (.GPR 31#5) u).toNat := by rw [usp]; exact hs
    let t := block base (arenaLayoutOps u) u
    have ht := arena_layout_run u base (eu.2.2.2.code base hc)
      (eu.2.2.2.error.trans he) (eu.2.2.2.aligned ha) upc
    have et := arena_layout_effect u base us
    have bytes : (arenaLayoutBytes u).toNat = 8 * ((r (.GPR 8#5) s).toNat + 1) := by
      rw [arena_layout_bytes u (by rw [eu.2.1]; exact limit), eu.2.1]
    refine ⟨3 + 9, t, ?_, eu.2.2.2.trans et.2.2.2.2.2, ?_,
      et.2.1.trans eu.2.1, ?_⟩
    · rw [run_plus, hu, ht]
    · intro a outside
      rw [← eu.2.2.1]
      exact arena_layout_memory u base us a (by rw [usp]; exact outside)
    · by_cases layout : 8 * ((r (.GPR 8#5) s).toNat + 1) < 2^63
      · exact Or.inr ⟨layout, et.1.trans (if_pos (by rw [bytes]; exact layout)),
          (congrArg BitVec.toNat et.2.2.2.1).trans bytes⟩
      · exact Or.inl ⟨layout, et.1.trans (if_neg (by rw [bytes]; exact layout))⟩
  · refine ⟨3, u, hu, eu.2.2.2, ?_, eu.2.1, Or.inl ⟨by omega, ?_⟩⟩
    · intro a outside
      rw [eu.2.2.1]
    · exact eu.1.trans (if_pos (by omega))

end SszArm.NatAdd
