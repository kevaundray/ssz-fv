import SszArm.NatDivisionExec
import SszArm.NatDivisionMemory

namespace SszArm.NatDivision

open BoolCodec
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Only physical separation, never execution-equivalent assumptions. -/
structure FailureOwned (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64
  separate : (r (.GPR 19#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 19#5) s).toNat

def failureOps : List Op :=
  [.p812, .p816, .p820, .p824, .p828, .p832, .p836, .p840,
   .p844, .p848, .p852, .p856, .p860, .p864, .p868, .p872,
   .p876, .p880, .p884, .p888, .p892, .p896, .p900, .p904,
   .p908, .p912, .p916, .p920, .p924, .p928, .p932, .p936,
   .p940, .p944, .p948, .p952, .p956, .p960, .p964, .p968, .p972]

def failureResult (base : BitVec 64) (s : ArmState) : ArmState := block base failureOps s

def failureWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 19#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 16, 16)]

macro "natdiv_failure_side" : tactic => `(tactic|
  first | assumption | omega | bv_omega)

macro "natdiv_failure_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [failureResult, failureOps, block, List.foldl_cons, List.foldl_nil,
     Op.effect, put, next, state_simp_rules, ArmState.mem_w_eq_mem,
     BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat,
     Nat.reduceAdd, BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

macro "natdiv_failure_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := natdiv_failure_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

theorem failure_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 812#64) : run 41 s = failureResult base s := by
  apply block_run base failureOps s hc he ha
  have hpc : r .PC s = base + 812#64 := hp
  simp [failureOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem failure_pc (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 812#64) : read_pc (failureResult base s) = base + 976#64 := by
  have hpc : r .PC s = base + 812#64 := hp
  natdiv_failure_expand
  simp [hpc, BitVec.add_assoc]

theorem failure_registers (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (hr : reg ∉ [1#5, 8#5, 9#5, 10#5, 31#5]) :
    r (.GPR reg) (failureResult base s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp (disch := simp_all) [failureResult, failureOps, block, Op.effect,
    put, next, state_simp_rules]

@[simp] theorem failure_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (failureResult base s) = r (.GPR 31#5) s := by
  natdiv_failure_expand

/-- The common return consumes these exact argument registers: it writes zero
at output+8 and the four-byte reason at output+64. -/
theorem failure_arguments (s : ArmState) (base : BitVec 64) (owned : FailureOwned s) :
    r (.GPR 1#5) (failureResult base s) = 0#64 ∧
    r (.GPR 8#5) (failureResult base s) = 32768#64 ∧
    r (.GPR 9#5) (failureResult base s) = 8#64 ∧
    r (.GPR 10#5) (failureResult base s) = 1#64 := by
  obtain ⟨stack, output, separate⟩ := owned
  refine ⟨?_, ?_, ?_, ?_⟩ <;> natdiv_failure_expand <;> natdiv_failure_reads

/-- Six zero words and the non-null empty text pointer are fully written before
entering the common return. Bytes8..15 and the reason are written there. -/
theorem failure_image (s : ArmState) (base : BitVec 64) (owned : FailureOwned s) :
    read_mem_bytes 8 (r (.GPR 19#5) s) (failureResult base s) = 1#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) (failureResult base s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 24#64) (failureResult base s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 32#64) (failureResult base s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 40#64) (failureResult base s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 48#64) (failureResult base s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 56#64) (failureResult base s) = 0#64 := by
  obtain ⟨stack, output, separate⟩ := owned
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> natdiv_failure_expand <;> natdiv_failure_reads

/-- No allocation and no arena mutation occur on this entire phase. -/
theorem failure_frame (s : ArmState) (base : BitVec 64) (owned : FailureOwned s) :
    MemoryFrame (failureWrites s) s (failureResult base s) := by
  obtain ⟨stack, output, separate⟩ := owned
  intro a outside
  have out := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [failureWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [failureWrites])
  natdiv_failure_expand
  natdiv_failure_reads
  simp (disch := natdiv_failure_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

/-- Lifts the leaf's precise spill frame into the original 80-byte activation. -/
theorem failure_local_frame (original s : ArmState) (base : BitVec 64)
    (owned : FailureOwned s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (stack : (r (.GPR 31#5) s).toNat + 64 = (r (.GPR 31#5) original).toNat) :
    MemoryFrame (localWrites original) s (failureResult base s) := by
  intro a outside
  apply failure_frame s base owned a
  intro span member
  simp only [failureWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa only [out] using outside ((r (.GPR 0#5) original).toNat, 68) (by simp [localWrites])
  · have h := outside ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
    have bound := owned.stack
    simp only [Prod.fst, Prod.snd] at *
    omega

theorem failure_operand_preserved (s : ArmState) (base : BitVec 64)
    (owned : FailureOwned s) (operand : SszNative.NatOperand)
    (input : operand.At (widthLoad s)) (inputOwned : OperandOwned (failureWrites s) operand) :
    OperandPreserved s (failureResult base s) operand :=
  operand_preserved (failure_frame s base owned) operand input inputOwned

end SszArm.NatDivision
