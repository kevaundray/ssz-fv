import SszArm.NatMulWordHighFrame
import SszArm.NatMulWordReserveFirst
import SszArm.NatMulLoopMemoryFrame

namespace SszArm.NatMulWord.Large

open Delimited (MemoryFrame)

def firstStoreOps : List Op := [.p592, .p596]

def firstCompleted (s : ArmState) (base : BitVec 64) : ArmState :=
  block base firstStoreOps (highCompleted .first s base)

structure FirstPost (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 812#64
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ≠ 14#5 → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  carry : r (.GPR 14#5) t = NatMulProduct.high (r (.GPR 14#5) s) (r (.GPR 3#5) s)
  words : NatCompare.Words t (r (.GPR 10#5) s) [r (.GPR 11#5) s]
  frame : MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48), ((r (.GPR 10#5) s).toNat, 8)] s t

theorem FirstPost.sp {s t : ArmState} {base : BitVec 64} (post : FirstPost s t base) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := post.registers _ (by decide)

theorem FirstPost.code {s t : ArmState} {base : BitVec 64} (post : FirstPost s t base)
    (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, post.program] using code

theorem FirstPost.aligned {s t : ArmState} {base : BitVec 64} (post : FirstPost s t base)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, post.sp] using aligned

theorem first_store_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 592#64) : run 2 s = block base firstStoreOps s := by
  apply block_run base firstStoreOps s code error aligned
  have hpc : r .PC s = base + 592#64 := pc
  simp [firstStoreOps, Follows, Op.row, Op.effect, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem first_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 480#64) : run 30 s = firstCompleted s base := by
  let u := highCompleted .first s base
  have uc : CodeAt u base := by simpa only [CodeAt, u, highCompleted, block_program] using code
  have ue : read_err u = .None := by simpa only [u, highCompleted, block_error] using error
  have ua : CheckSPAlignment u :=
    block_aligned _ _ _ (block_aligned _ _ _ (block_aligned _ _ _ aligned))
  have upc : read_pc u = base + 592#64 := by
    rw [show u = highCompleted .first s base from rfl, high_completed_pc, pc]
    simp [BitVec.add_assoc]
  change run (28 + 2) s = _
  rw [run_plus, high_run .first s base code error aligned pc, first_store_run u base uc ue ua upc]
  rfl

theorem first_memory (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    (firstCompleted s base).mem =
      (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 11#5) s) (HighSite.first.spilled s)).mem := by
  have address := high_completed_registers .first s base stack 10#5 (by decide)
  have value := high_completed_registers .first s base stack 11#5 (by decide)
  simp only [firstCompleted, firstStoreOps, block, List.foldl_cons, List.foldl_nil,
    Op.effect, next, ArmState.mem_w_eq_mem, address, value]
  exact mem_write_mem_bytes_of_mem_eq (high_completed_memory .first s base) _ _ _

/-- Genuine high-product lowering, first destination store, and branch to the
loop head. No previous destination observation is needed. -/
theorem first_contract (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 10#5) s).toNat + 8 ≤ 2^64) :
    FirstPost s (firstCompleted s base) base := by
  have hm := first_memory s base stack
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [firstCompleted, firstStoreOps, block, Op.effect, next, state_simp_rules]
  · simp only [firstCompleted, block_program, highCompleted, block_program]
  · simp only [firstCompleted, block_error, highCompleted, block_error]
  · intro reg different
    simpa only [firstCompleted, firstStoreOps, block, List.foldl_cons, List.foldl_nil,
      Op.effect, next, state_simp_rules] using
      high_completed_registers .first s base stack reg different
  · intro reg
    have preserves : ∀ ops t, r (.SFP reg) (block base ops t) = r (.SFP reg) t := by
      intro ops t
      exact Reserve.block_preserves (r (.SFP reg)) base ops (fun op _ v => op.sfp base v reg) t
    simp only [firstCompleted, highCompleted, preserves]
  · simpa only [firstCompleted, firstStoreOps, block, List.foldl_cons, List.foldl_nil,
      Op.effect, next, state_simp_rules] using high_completed_value .first s base
  · intro i
    have zero : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
    simp only [zero, Nat.mul_zero, BitVec.ofNat_zero, BitVec.add_zero]
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp hm]
    simpa [zero] using BoolCodec.read_mem_bytes_write_mem_bytes_same
      (HighSite.first.spilled s) 8 (r (.GPR 10#5) s) (r (.GPR 11#5) s) physical
  · intro address outside
    rw [hm, BoolCodec.write_mem_bytes_frame _ _ _ _ address physical
      (outside ((r (.GPR 10#5) s).toNat, 8) (by simp))]
    have frame := high_completed_frame .first s base stack address (by
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      exact outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp))
    simpa only [high_completed_memory] using frame

end SszArm.NatMulWord.Large
