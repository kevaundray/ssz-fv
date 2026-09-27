import SszArm.DelimitedBlocks
import SszArm.DelimitedMemory
import SszArm.UintResultMemory

namespace SszArm.Delimited

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Only the reservation scratch registers and the returned Nat pair change. -/
structure ArenaFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 19#5, 20#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem ArenaFrame.refl (s : ArmState) : ArenaFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem ArenaFrame.trans {s t u : ArmState} (st : ArenaFrame s t)
    (tu : ArenaFrame t u) : ArenaFrame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem ArenaFrame.sp {s t : ArmState} (frame : ArenaFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem ArenaFrame.aligned {s t : ArmState} (frame : ArenaFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem ArenaFrame.code {s t : ArmState} (frame : ArenaFrame s t)
    (base : BitVec 64) (hc : CodeAt s base) : CodeAt t base := by
  intro row hr
  simpa only [frame.program] using hc row hr

/-- The four instructions before the first Option tag read. -/
def arenaStoreOps : List Op := [.p336, .p340, .p344, .p348]

theorem arenaStore_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 336#64) :
    run 4 s = block base arenaStoreOps s := by
  apply block_run base arenaStoreOps s hc he ha
  have hpc : r .PC s = base + 336#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaStoreOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

def arenaCommitPointer (s : ArmState) : BitVec 64 :=
  r (.GPR 8#5) s + r (.GPR 9#5) s

def arenaCommitMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (arenaCommitPointer s)
    (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
    (write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (r (.GPR 10#5) s) s)

def arenaCommitWrites (s : ArmState) : List Span :=
  [((r (.GPR 4#5) s + 16#64).toNat, 8), ((arenaCommitPointer s).toNat, 16)]

/-- Physical ownership covers just the cursor word and the fresh payload. It
requires neither a small arena capacity nor separation of immutable aliases. -/
def ArenaCommitOwned (s : ArmState) : Prop :=
  (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ 2^64 ∧
  0 < (arenaCommitPointer s).toNat ∧
  (arenaCommitPointer s).toNat % 8 = 0 ∧
  (arenaCommitPointer s).toNat + 16 ≤ 2^64 ∧
  ((r (.GPR 4#5) s + 16#64).toNat + 8 ≤ (arenaCommitPointer s).toNat ∨
    (arenaCommitPointer s).toNat + 16 ≤ (r (.GPR 4#5) s + 16#64).toNat)

theorem arena_store_frame (s : ArmState) (base : BitVec 64) :
    ArenaFrame s (block base arenaStoreOps s) := by
  constructor
  · exact block_program _ _ _
  · exact block_error _ _ _
  · intro reg notChanged
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notChanged
    simp (disch := simp_all) [arenaStoreOps, block, Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [arenaStoreOps, block, Op.effect, put, next, state_simp_rules]

/-- Cursor commitment is proved with abstract source memory: register updates
are erased before the store-congruence lemma is instantiated. -/
private theorem arena_cursor_commit (s t : ArmState) (base header cursor : BitVec 64)
    (memory : s.mem = t.mem) (h4 : r (.GPR 4#5) s = header)
    (h10 : r (.GPR 10#5) s = cursor) :
    (Op.effect base .p344 s).mem = (write_mem_bytes 8 (header + 16#64) cursor t).mem ∧
      r (.GPR 20#5) (Op.effect base .p344 s) = r (.GPR 20#5) s ∧
      r (.GPR 23#5) (Op.effect base .p344 s) = r (.GPR 23#5) s ∧
      r (.GPR 24#5) (Op.effect base .p344 s) = r (.GPR 24#5) s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Op.effect, next, ArmState.mem_w_eq_mem, h4, h10] using
      mem_write_mem_bytes_of_mem_eq memory 8 (header + 16#64) cursor
  · simp [Op.effect, next, state_simp_rules]
  · simp [Op.effect, next, state_simp_rules]
  · simp [Op.effect, next, state_simp_rules]

/-- The paired-store congruence is opaque before it sees a composed state. -/
private theorem arena_payload_commit (s t : ArmState) (base pointer low high : BitVec 64)
    (memory : s.mem = t.mem) (h20 : r (.GPR 20#5) s = pointer)
    (h24 : r (.GPR 24#5) s = low) (h23 : r (.GPR 23#5) s = high) :
    (Op.effect base .p348 s).mem = (write_mem_bytes 16 pointer (high ++ low) t).mem := by
  simpa only [Op.effect, next, ArmState.mem_w_eq_mem, h20, h24, h23] using
    mem_write_mem_bytes_of_mem_eq memory 16 pointer (high ++ low)

/-- An opaque four-instruction effect, including the exact order of the stores. -/
theorem arena_store_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 336#64) :
    let t := block base arenaStoreOps s
    read_pc t = base + 352#64 ∧
      r (.GPR 20#5) t = arenaCommitPointer s ∧ r (.GPR 19#5) t = 2#64 ∧
      t.mem = (arenaCommitMemory s).mem := by
  have hpc : r .PC s = base + 336#64 := hp
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [arenaStoreOps, block, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc]
  · simp [arenaStoreOps, arenaCommitPointer, block, Op.effect, put, next, state_simp_rules]
  · simp [arenaStoreOps, block, Op.effect, put, next, state_simp_rules]
  · let prepared := Op.effect base .p340 (Op.effect base .p336 s)
    have observations : prepared.mem = s.mem ∧
        r (.GPR 4#5) prepared = r (.GPR 4#5) s ∧
        r (.GPR 10#5) prepared = r (.GPR 10#5) s ∧
        r (.GPR 20#5) prepared = arenaCommitPointer s ∧
        r (.GPR 23#5) prepared = r (.GPR 23#5) s ∧
        r (.GPR 24#5) prepared = r (.GPR 24#5) s := by
      simp [prepared, Op.effect, put, next, arenaCommitPointer,
        state_simp_rules, ArmState.mem_w_eq_mem]
    have cursor := arena_cursor_commit prepared s base (r (.GPR 4#5) s)
      (r (.GPR 10#5) s) observations.1 observations.2.1 observations.2.2.1
    have payload := arena_payload_commit (Op.effect base .p344 prepared)
      (write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (r (.GPR 10#5) s) s)
      base (arenaCommitPointer s) (r (.GPR 24#5) s) (r (.GPR 23#5) s) cursor.1
      (cursor.2.1.trans observations.2.2.2.1)
      (cursor.2.2.2.trans observations.2.2.2.2.2)
      (cursor.2.2.1.trans observations.2.2.2.2.1)
    have blockEq : block base arenaStoreOps s =
        Op.effect base .p348 (Op.effect base .p344 prepared) := rfl
    rw [blockEq]
    exact payload

theorem arena_commit_memory_frame (s : ArmState) (owned : ArenaCommitOwned s) :
    MemoryFrame (arenaCommitWrites s) s (arenaCommitMemory s) := by
  intro a outside
  have hc := outside ((r (.GPR 4#5) s + 16#64).toNat, 8) (by simp [arenaCommitWrites])
  have hp := outside ((arenaCommitPointer s).toNat, 16) (by simp [arenaCommitWrites])
  unfold arenaCommitMemory
  rw [BoolCodec.write_mem_bytes_frame _ _ _ _ a owned.2.2.2.1 hp,
    BoolCodec.write_mem_bytes_frame _ _ _ _ a owned.1 hc]

/-- The architectural paired store supplies both little-endian Nat limbs. -/
theorem arena_pair_store (s : ArmState) (pointer low high : BitVec 64)
    (positive : 0 < pointer.toNat) (aligned : pointer.toNat % 8 = 0)
    (physical : pointer.toNat + 16 ≤ 2^64) :
    SszNative.NatMemory.Pair
      (widthLoad (write_mem_bytes 16 pointer (high ++ low) s)) pointer 2#64
      (low.toNat + 2^64 * high.toNat) := by
  rw [UintCodec.Tail.write_pair_words s pointer low high physical]
  refine Or.inr ⟨[low, high], positive, aligned, ?_, rfl, ?_, ?_⟩
  · simpa using physical
  · intro i
    have hi : i.val < 2 := i.isLt
    have cases : i.val = 0 ∨ i.val = 1 := by omega
    rcases cases with hi0 | hi1
    · simp only [widthLoad, hi0, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 pointer
        (pointer + 8#64) high (by omega) (by bv_omega) (by left; bv_omega),
        BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 pointer low (by omega)]
      simp [hi0]
    · have addr : BitVec.ofNat 64 (pointer.toNat + 8 * i.val) = pointer + 8#64 := by
        rw [hi1]
        bv_omega
      simp only [widthLoad, addr]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 (pointer + 8#64) high (by bv_omega)]
      simp [hi1]
  · simp [SszNative.Limbs.value]

/-- Commitment observes the exact new cursor, frames every other byte, and
constructs the native two-limb Nat before any optional limit is read. -/
theorem arena_store_memory (s : ArmState) (base : BitVec 64)
    (owned : ArenaCommitOwned s) (hp : read_pc s = base + 336#64) :
    let t := block base arenaStoreOps s
    MemoryFrame (arenaCommitWrites s) s t ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t = r (.GPR 10#5) s ∧
      SszNative.NatMemory.Pair (widthLoad t) (arenaCommitPointer s) 2#64
        ((r (.GPR 24#5) s).toNat + 2^64 * (r (.GPR 23#5) s).toNat) := by
  dsimp only
  have hm := (arena_store_effect s base hp).2.2.2
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp hm
  refine ⟨?_, ?_, ?_⟩
  · intro a outside
    rw [hm]
    exact arena_commit_memory_frame s owned a outside
  · rw [reads]
    unfold arenaCommitMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16
      (r (.GPR 4#5) s + 16#64) (arenaCommitPointer s) _ owned.1 owned.2.2.2.1 owned.2.2.2.2,
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ owned.1]
  · have loadEq : widthLoad (block base arenaStoreOps s) = widthLoad (arenaCommitMemory s) := by
      funext address bytes
      unfold widthLoad
      rw [reads]
    rw [loadEq]
    exact arena_pair_store _ _ _ _ owned.2.1 owned.2.2.1 owned.2.2.2.1

end SszArm.Delimited
