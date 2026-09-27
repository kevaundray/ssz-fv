import SszArm.NatAddArenaReserve
import SszArm.NatCompareMemory
import SszArm.DelimitedArenaCommit

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def arenaBigStoreOps : List Op := [.p268, .p272]
def arenaSmallStoreOps : List Op := [.p1180, .p1184, .p1188, .p1192]

def arenaBigMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 5#5) s + 16#64) (r (.GPR 11#5) s) s

def arenaSmallPointer (s : ArmState) : BitVec 64 := r (.GPR 8#5) s + r (.GPR 10#5) s

def arenaSmallMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (arenaSmallPointer s) (1#64 ++ r (.GPR 9#5) s) (arenaBigMemory s)

theorem arena_big_store_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 268#64) :
    run 2 s = block base arenaBigStoreOps s := by
  apply block_run base arenaBigStoreOps s hc he ha
  have hpc : r .PC s = base + 268#64 := hp
  simp [arenaBigStoreOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem arena_small_store_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1180#64) :
    run 4 s = block base arenaSmallStoreOps s := by
  apply block_run base arenaSmallStoreOps s hc he ha
  have hpc : r .PC s = base + 1180#64 := hp
  simp [arenaSmallStoreOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem arena_big_store_frame (s : ArmState) (base : BitVec 64) :
    ArenaFrame s (block base arenaBigStoreOps s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [arenaBigStoreOps, block, Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [arenaBigStoreOps, block, Op.effect, put, next, state_simp_rules]

theorem arena_small_store_frame (s : ArmState) (base : BitVec 64) :
    ArenaFrame s (block base arenaSmallStoreOps s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [arenaSmallStoreOps, block, Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [arenaSmallStoreOps, block, Op.effect, put, next, state_simp_rules]

theorem arena_big_store_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 268#64) :
    let t := block base arenaBigStoreOps s
    read_pc t = base + 276#64 ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s + r (.GPR 12#5) s ∧
      r (.GPR 11#5) t = r (.GPR 11#5) s ∧ t.mem = (arenaBigMemory s).mem := by
  have hpc : r .PC s = base + 268#64 := hp
  simp [arenaBigStoreOps, arenaBigMemory, block, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc, NatCompare.spill_mem_w]

theorem arena_small_store_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 1180#64) :
    let t := block base arenaSmallStoreOps s
    read_pc t = base + 1196#64 ∧
      r (.GPR 8#5) t = arenaSmallPointer s ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧ r (.GPR 10#5) t = 1#64 ∧
      t.mem = (arenaSmallMemory s).mem := by
  have hpc : r .PC s = base + 1180#64 := hp
  simp [arenaSmallStoreOps, arenaSmallMemory, arenaSmallPointer, arenaBigMemory,
    block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc,
    NatCompare.spill_mem_w]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [NatCompare.spill_mem_w]

/-- Only the cursor word is committed before the large-limb loop begins. -/
theorem arena_big_store_memory (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64)
    (hp : read_pc s = base + 268#64) :
    let t := block base arenaBigStoreOps s
    Delimited.MemoryFrame [((r (.GPR 5#5) s + 16#64).toNat, 8)] s t ∧
      read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = r (.GPR 11#5) s := by
  dsimp only
  have hm := (arena_big_store_effect s base hp).2.2.2
  constructor
  · intro a outside
    rw [hm]
    apply BoolCodec.write_mem_bytes_frame _ _ _ _ a physical
    exact outside ((r (.GPR 5#5) s + 16#64).toNat, 8) (by simp)
  · rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp hm]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ physical

/-- Fresh payload ownership does not impose any signed bound on arena capacity. -/
def ArenaSmallOwned (s : ArmState) : Prop :=
  (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64 ∧
  0 < (arenaSmallPointer s).toNat ∧
  (arenaSmallPointer s).toNat % 8 = 0 ∧
  (arenaSmallPointer s).toNat + 16 ≤ 2^64 ∧
  ((r (.GPR 5#5) s + 16#64).toNat + 8 ≤ (arenaSmallPointer s).toNat ∨
    (arenaSmallPointer s).toNat + 16 ≤ (r (.GPR 5#5) s + 16#64).toNat)

theorem arena_small_store_memory (s : ArmState) (base : BitVec 64)
    (owned : ArenaSmallOwned s) (hp : read_pc s = base + 1180#64) :
    let t := block base arenaSmallStoreOps s
    Delimited.MemoryFrame
      [((r (.GPR 5#5) s + 16#64).toNat, 8), ((arenaSmallPointer s).toNat, 16)] s t ∧
      read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = r (.GPR 11#5) s ∧
      SszNative.NatMemory.Pair (widthLoad t) (arenaSmallPointer s) 2#64
        ((r (.GPR 9#5) s).toNat + 2^64) := by
  dsimp only
  have hm := (arena_small_store_effect s base hp).2.2.2.2
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp hm
  refine ⟨?_, ?_, ?_⟩
  · intro a outside
    rw [hm]
    have cursor := outside ((r (.GPR 5#5) s + 16#64).toNat, 8) (by simp)
    have payload := outside ((arenaSmallPointer s).toNat, 16) (by simp)
    unfold arenaSmallMemory arenaBigMemory
    rw [BoolCodec.write_mem_bytes_frame _ _ _ _ a owned.2.2.2.1 payload,
      BoolCodec.write_mem_bytes_frame _ _ _ _ a owned.1 cursor]
  · rw [reads]
    unfold arenaSmallMemory arenaBigMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16
      (r (.GPR 5#5) s + 16#64) (arenaSmallPointer s) _ owned.1 owned.2.2.2.1 owned.2.2.2.2,
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ owned.1]
  · have loadEq : widthLoad (block base arenaSmallStoreOps s) = widthLoad (arenaSmallMemory s) := by
      funext address bytes
      unfold widthLoad
      rw [reads]
    rw [loadEq]
    simpa [arenaSmallMemory] using Delimited.arena_pair_store (arenaBigMemory s)
      (arenaSmallPointer s) (r (.GPR 9#5) s) 1#64 owned.2.1 owned.2.2.1 owned.2.2.2.1

end SszArm.NatAdd
