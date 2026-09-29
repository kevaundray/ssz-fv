import SszArm.HashCombineRightDrain
import SszArm.HashCombineMetadata

namespace SszArm.Hash.Combine

@[simp] theorem rightGuard_memory (s : ArmState) : (rightGuard s).mem = s.mem := by
  simp [rightGuard, rightGuardOps, block, Op.effect, compare, branch, next, state_simp_rules]

@[simp] theorem rightGuard_register (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (rightGuard s) = r (.GPR reg) s := by
  simp [rightGuard, rightGuardOps, block, Op.effect, compare, branch, next, state_simp_rules]

theorem rightGuard_local (s : ArmState) (error : read_err s = .None) : LocalPost s (rightGuard s) := by
  refine ⟨?_, ?_, rightGuard_register s 31#5, rightGuard_register s 19#5,
    rightGuard_register s 24#5, ?_, ?_, ?_⟩
  · simpa only [rightGuard, block_error] using error
  · simp only [rightGuard, block_program]
  · intro reg lo hi
    exact rightGuard_register s reg
  · intro reg lo hi
    simp [rightGuard, rightGuardOps, block, Op.effect, compare, branch, next, state_simp_rules]
  · intro address outside
    exact congrFun (rightGuard_memory s) address

theorem rightGuard_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 308#64) :
    read_pc (rightGuard s) = if 64 ≤ (r (.GPR 20#5) s).toNat then base + 316#64 else base + 344#64 := by
  change r .PC s = _ at pc
  by_cases enough : 64 ≤ (r (.GPR 20#5) s).toNat
  · have carry := (Udivti3.cmp_carry (r (.GPR 20#5) s) 64#64).mpr enough
    simp (config := {decide := true, instances := true})
      [rightGuard, rightGuardOps, block, Op.effect, next, compare, branch,
        state_simp_rules, pc, BitVec.add_assoc, carry, enough]
  · have carry : (AddWithCarry (r (.GPR 20#5) s) (~~~64#64) 1#1).2.c ≠ 1#1 := by
      intro h
      exact enough ((Udivti3.cmp_carry (r (.GPR 20#5) s) 64#64).mp h)
    simp (config := {decide := true, instances := true})
      [rightGuard, rightGuardOps, block, Op.effect, next, compare, branch,
        state_simp_rules, pc, BitVec.add_assoc, carry, enough]

theorem right_guard_drain_correct (origin s : ArmState) (base : BitVec 64)
    (left right : ByteArray) (start : Nat) (startBound : start ≤ right.size)
    (buffer : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (code : CodeAt origin base) (data : DataAt origin base) (compression : CompressionCorrect base)
    (owned : CombineOwned origin base left right) (activation : Activation origin s)
    (pc : read_pc s = base + 308#64)
    (bufferAt : BytesAt s (r (.GPR 31#5) s) ⟨buffer.toArray⟩)
    (chaining : ChainingAt s (r (.GPR 31#5) s + 64#64) words)
    (lengthAt : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s = byteLen.toBitVec)
    (cursor : r (.GPR 21#5) s = r (.GPR 3#5) origin + BitVec.ofNat 64 start)
    (count : (r (.GPR 20#5) s).toNat = right.size - start) :
    ∃ fuel, let t := run fuel s
      Activation origin t ∧ read_pc t = base + 364#64 ∧
      StateAt t (r (.GPR 31#5) t)
        (SszNative.HashStream.drain buffer words byteLen right start startBound).state := by
  let u := rightGuard s
  have post := rightGuard_local s activation.error
  have uActivation := activation.after owned.stackLow post
  have uPC : read_pc u = if (right.size - start) / 64 = 0 then base + 344#64 else base + 316#64 := by
    rw [rightGuard_pc s base pc, count]
    by_cases enough : 64 ≤ right.size - start
    · simp only [if_pos enough, if_neg (by omega : ¬ (right.size - start) / 64 = 0)]
    · simp only [if_neg enough, if_pos (by omega : (right.size - start) / 64 = 0)]
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (rightGuard_memory s)
  obtain ⟨fuel, result⟩ := right_drain_correct origin u base left right start startBound buffer words byteLen
    code data compression owned uActivation uPC
    (by simpa only [u, BytesAt, rightGuard_register, rightGuard_memory] using bufferAt)
    (by simpa only [u, ChainingAt, rightGuard_register, reads] using chaining)
    (by simpa only [u, rightGuard_register, reads] using lengthAt)
    (by simpa only [u, rightGuard_register] using cursor)
    (by simpa only [u, rightGuard_register] using count)
  refine ⟨2 + fuel, ?_⟩
  rw [run_plus, rightGuard_run s base (activation.code code) activation.error activation.aligned pc]
  exact result

end SszArm.Hash.Combine
