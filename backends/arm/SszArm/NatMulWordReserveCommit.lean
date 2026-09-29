import SszArm.NatMulWordReserveHeader
import SszArm.NatAddMemory
import SszArm.NatCompareMemory
import SszArm.DelimitedArenaCommit

namespace SszArm.NatMulWord.Reserve

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

def wideCommitOps : List Op := [.p1200, .p1204, .p1208, .p1212]

def widePointer (s : ArmState) : BitVec 64 := r (.GPR 10#5) s + r (.GPR 11#5) s

def wideCommitMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (widePointer s) (r (.GPR 9#5) s ++ r (.GPR 8#5) s)
    (write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (r (.GPR 12#5) s) s)

def wideCommitWrites (s : ArmState) : List Span :=
  [((r (.GPR 4#5) s + 16#64).toNat, 8), ((widePointer s).toNat, 16)]

structure WideSpace (s : ArmState) : Prop where
  header : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  positive : 0 < (widePointer s).toNat
  aligned : (widePointer s).toNat % 8 = 0
  payload : (widePointer s).toNat + 16 ≤ 2^64
  separate : (r (.GPR 4#5) s).toNat + 24 ≤ (widePointer s).toNat ∨
    (widePointer s).toNat + 16 ≤ (r (.GPR 4#5) s).toNat

theorem wide_commit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1200#64) :
    run 4 s = block base wideCommitOps s := by
  apply block_run base wideCommitOps s hc he ha
  have hpc : r .PC s = base + 1200#64 := hp
  simp [wideCommitOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem wide_commit_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 1200#64) :
    let t := block base wideCommitOps s
    read_pc t = base + 1216#64 ∧ r (.GPR 10#5) t = widePointer s ∧
      r (.GPR 8#5) t = 2#64 ∧ t.mem = (wideCommitMemory s).mem := by
  have hpc : r .PC s = base + 1200#64 := hp
  simp [wideCommitOps, widePointer, wideCommitMemory, block, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc, NatCompare.spill_mem_w]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [NatCompare.spill_mem_w]

theorem wide_commit_registers (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (keep : reg ≠ 8#5 ∧ reg ≠ 10#5) :
    r (.GPR reg) (block base wideCommitOps s) = r (.GPR reg) s := by
  simp [wideCommitOps, block, Op.effect, put, next, state_simp_rules, keep.1, keep.2]

theorem wide_commit_memory (s : ArmState) (base : BitVec 64)
    (space : WideSpace s) (hp : read_pc s = base + 1200#64) :
    let t := block base wideCommitOps s
    MemoryFrame (wideCommitWrites s) s t ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t = r (.GPR 12#5) s ∧
      read_mem_bytes 8 (r (.GPR 4#5) s) t = read_mem_bytes 8 (r (.GPR 4#5) s) s ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t = read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s ∧
      (SszNative.NatOperand.large (widePointer s) [r (.GPR 8#5) s, r (.GPR 9#5) s]).At (widthLoad t) := by
  dsimp only
  have hm := (wide_commit_effect s base hp).2.2.2
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp hm
  have header := space.header
  have payload := space.payload
  have separate := space.separate
  have cursor : (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ 2^64 := by bv_omega
  refine ⟨?_, ?_, ?_, ?_, space.positive, space.aligned, ?_, ?_⟩
  · intro a outside
    rw [hm]
    have hc := outside ((r (.GPR 4#5) s + 16#64).toNat, 8) (by simp [wideCommitWrites])
    have hp := outside ((widePointer s).toNat, 16) (by simp [wideCommitWrites])
    unfold wideCommitMemory
    rw [BoolCodec.write_mem_bytes_frame _ _ _ _ a payload hp,
      BoolCodec.write_mem_bytes_frame _ _ _ _ a cursor hc]
  · rw [reads]
    unfold wideCommitMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16 _ _ _
      cursor payload (by bv_omega),
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ cursor]
  · rw [reads]
    unfold wideCommitMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16 _ _ _
      (by omega) payload (by bv_omega),
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by omega) cursor (by bv_omega)]
  · rw [reads]
    unfold wideCommitMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16 _ _ _
      (by bv_omega) payload (by bv_omega),
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) cursor (by bv_omega)]
  · simpa using payload
  · intro i
    have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; simp only [List.length_cons, List.length_nil] at this; omega
    have pair := UintCodec.Tail.write_pair_words
      (write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (r (.GPR 12#5) s) s)
      (widePointer s) (r (.GPR 8#5) s) (r (.GPR 9#5) s) payload
    rcases hi with hi | hi
    · simp only [widthLoad, hi, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat]
      arm_word_nf
      rw [reads]
      unfold wideCommitMemory
      rw [pair, BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by omega) (by bv_omega) (by bv_omega),
        BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by omega)]
      simp [hi]
    · have address : BitVec.ofNat 64 ((widePointer s).toNat + 8 * i.val) = widePointer s + 8#64 := by
        rw [hi]
        bv_omega
      simp only [widthLoad, address]
      rw [reads]
      unfold wideCommitMemory
      rw [pair, BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)]
      simp [hi]

theorem wide_commit_input (s : ArmState) (base : BitVec 64)
    (space : WideSpace s) (hp : read_pc s = base + 1200#64)
    (operand : SszNative.NatOperand) (input : operand.At (widthLoad s))
    (owned : NatAdd.OperandOwned (wideCommitWrites s) operand) :
    NatAdd.OperandPreserved s (block base wideCommitOps s) operand :=
  NatAdd.operand_preserved (wide_commit_memory s base space hp).1 operand input owned

/-- Current free-suffix ownership, with no successful-allocation premise. -/
structure ArenaOwned (s : ArmState) (address capacity used : BitVec 64) : Prop where
  header : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  storage : address.toNat + capacity.toNat ≤ 2^64
  nonnull : 0 < capacity.toNat → 0 < address.toNat
  freeHeader : Protected [((r (.GPR 4#5) s).toNat, 24)]
    (address.toNat + used.toNat) (capacity.toNat - used.toNat)

theorem ArenaOwned.wideSpace {s t : ArmState} {address capacity used : BitVec 64}
    (owned : ArenaOwned s address capacity used) (reached : Checkpoint s t)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2)
    (baseReg : r (.GPR 10#5) t = address)
    (startReg : (r (.GPR 11#5) t).toNat = SszNative.Arena.start address.toNat used.toNat) :
    WideSpace t ∧ (widePointer t).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat := by
  have start := SszNative.Arena.used_le_start address.toNat used.toNat
  have finish := checks.2.2.2.2.2
  have finishEq : SszNative.Arena.finish address.toNat used.toNat 2 =
      SszNative.Arena.start address.toNat used.toNat + 16 := rfl
  have storage := owned.storage
  have positive := owned.nonnull (by omega)
  have pointerNat : (widePointer t).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat := by
    simp only [widePointer, BitVec.toNat_add, baseReg, startReg]
    exact Nat.mod_eq_of_lt (by omega)
  have hdr := reached.frame.registers 4#5 (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, pointerNat⟩
  · simpa only [hdr] using owned.header
  · rw [pointerNat]; omega
  · rw [pointerNat, SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  · rw [pointerNat]; omega
  · rcases owned.freeHeader with empty | separate
    · omega
    · have sep := separate ((r (.GPR 4#5) s).toNat, 24) (by simp)
      rw [pointerNat, hdr]
      omega

end SszArm.NatMulWord.Reserve
