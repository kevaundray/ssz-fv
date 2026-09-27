import SszArm.NatDivisionArenaReserve
import SszArm.NatCompareMemory
import SszArm.DelimitedArenaCommit

namespace SszArm.NatDivision

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def arenaBigStoreOps : List Op := [.p284, .p288, .p292, .p296]
def arenaSmallStoreOps : List Op := [.p752, .p756, .p760, .p764]

def arenaBigMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 21#5) s + 16#64) (r (.GPR 12#5) s) s

def arenaSmallPointer (s : ArmState) : BitVec 64 := r (.GPR 8#5) s + r (.GPR 9#5) s

def arenaSmallCursorMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 21#5) s + 16#64) (r (.GPR 10#5) s) s

def arenaSmallMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (arenaSmallPointer s)
    (r (.GPR 1#5) s ++ r (.GPR 0#5) s) (arenaSmallCursorMemory s)

theorem arena_big_store_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 284#64) :
    run 4 s = block base arenaBigStoreOps s := by
  apply block_run base arenaBigStoreOps s hc he ha
  have hpc : r .PC s = base + 284#64 := hp
  simp [arenaBigStoreOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem arena_small_store_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 752#64) :
    run 4 s = block base arenaSmallStoreOps s := by
  apply block_run base arenaSmallStoreOps s hc he ha
  have hpc : r .PC s = base + 752#64 := hp
  simp [arenaSmallStoreOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem arena_big_store_registers (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (hr : reg ∉ [9#5, 24#5]) :
    r (.GPR reg) (block base arenaBigStoreOps s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp (disch := simp_all) [arenaBigStoreOps, block, Op.effect, put, next, state_simp_rules]

theorem arena_small_store_frame (s : ArmState) (base : BitVec 64) :
    ArenaFrame s (block base arenaSmallStoreOps s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [arenaSmallStoreOps, block, Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [arenaSmallStoreOps, block, Op.effect, put, next, state_simp_rules]

theorem arena_big_store_effect (s : ArmState) (base : BitVec 64) :
    let t := block base arenaBigStoreOps s
    read_pc t = base + 452#64 ∧
      r (.GPR 9#5) t = 0#64 ∧
      r (.GPR 24#5) t = r (.GPR 10#5) s + r (.GPR 11#5) s ∧
      t.mem = (arenaBigMemory s).mem := by
  simp [arenaBigStoreOps, arenaBigMemory, block, Op.effect, put, next,
    state_simp_rules, BitVec.add_assoc, NatCompare.spill_mem_w]

theorem arena_small_store_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 752#64) :
    let t := block base arenaSmallStoreOps s
    read_pc t = base + 768#64 ∧
      r (.GPR 9#5) t = arenaSmallPointer s ∧
      r (.GPR 10#5) t = 2#64 ∧
      t.mem = (arenaSmallMemory s).mem := by
  have hpc : r .PC s = base + 752#64 := hp
  simp [arenaSmallStoreOps, arenaSmallMemory, arenaSmallPointer, arenaSmallCursorMemory,
    block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc,
    NatCompare.spill_mem_w]

/-- The large path commits the cursor but writes no quotient byte yet. -/
theorem arena_big_store_memory (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 21#5) s + 16#64).toNat + 8 ≤ 2^64) :
    let t := block base arenaBigStoreOps s
    Delimited.MemoryFrame [((r (.GPR 21#5) s + 16#64).toNat, 8)] s t ∧
      read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) t = r (.GPR 12#5) s := by
  dsimp only
  have hm := (arena_big_store_effect s base).2.2.2
  constructor
  · intro a outside
    rw [hm]
    apply BoolCodec.write_mem_bytes_frame _ _ _ _ a physical
    exact outside ((r (.GPR 21#5) s + 16#64).toNat, 8) (by simp)
  · rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp hm]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ physical

/-- Physical allocation geometry; capacity is unsigned and the old cursor is unrestricted. -/
def ArenaSmallOwned (s : ArmState) : Prop :=
  (r (.GPR 21#5) s + 16#64).toNat + 8 ≤ 2^64 ∧
  0 < (arenaSmallPointer s).toNat ∧
  (arenaSmallPointer s).toNat % 8 = 0 ∧
  (arenaSmallPointer s).toNat + 16 ≤ 2^64 ∧
  ((r (.GPR 21#5) s + 16#64).toNat + 8 ≤ (arenaSmallPointer s).toNat ∨
    (arenaSmallPointer s).toNat + 16 ≤ (r (.GPR 21#5) s + 16#64).toNat)

theorem arena_small_store_memory (s : ArmState) (base : BitVec 64)
    (owned : ArenaSmallOwned s) (hp : read_pc s = base + 752#64) :
    let t := block base arenaSmallStoreOps s
    Delimited.MemoryFrame
      [((r (.GPR 21#5) s + 16#64).toNat, 8), ((arenaSmallPointer s).toNat, 16)] s t ∧
      read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) t = r (.GPR 10#5) s ∧
      SszNative.NatMemory.Pair (widthLoad t) (arenaSmallPointer s) 2#64
        ((r (.GPR 0#5) s).toNat + 2^64 * (r (.GPR 1#5) s).toNat) := by
  dsimp only
  have hm := (arena_small_store_effect s base hp).2.2.2
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp hm
  refine ⟨?_, ?_, ?_⟩
  · intro a outside
    rw [hm]
    have cursor := outside ((r (.GPR 21#5) s + 16#64).toNat, 8) (by simp)
    have payload := outside ((arenaSmallPointer s).toNat, 16) (by simp)
    unfold arenaSmallMemory arenaSmallCursorMemory
    rw [BoolCodec.write_mem_bytes_frame _ _ _ _ a owned.2.2.2.1 payload,
      BoolCodec.write_mem_bytes_frame _ _ _ _ a owned.1 cursor]
  · rw [reads]
    unfold arenaSmallMemory arenaSmallCursorMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16
      (r (.GPR 21#5) s + 16#64) (arenaSmallPointer s) _ owned.1 owned.2.2.2.1 owned.2.2.2.2,
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ owned.1]
  · have loadEq : widthLoad (block base arenaSmallStoreOps s) = widthLoad (arenaSmallMemory s) := by
      funext address bytes
      unfold widthLoad
      rw [reads]
    rw [loadEq]
    simpa [arenaSmallMemory] using Delimited.arena_pair_store (arenaSmallCursorMemory s)
      (arenaSmallPointer s) (r (.GPR 0#5) s) (r (.GPR 1#5) s)
      owned.2.1 owned.2.2.1 owned.2.2.2.1

end SszArm.NatDivision
