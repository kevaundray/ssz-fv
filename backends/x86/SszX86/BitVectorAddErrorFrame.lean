import SszX86.BitVectorAddError

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The exact write footprint is smaller than the caller's mutable work region. -/
theorem add_error_regions_frame (s : MachineData) (out : BitVec 64) (v : AddErrorImage)
    (outBound : out.toNat + 80 ≤ 2^64)
    (stageBound : (s.regs.rsp.toBitVec + 120#64).toNat + 64 ≤ 2^64) :
    RegionsFrame s.dmem (addErrorState s out v).dmem
      [(out.toNat, 80), ((s.regs.rsp.toBitVec + 120#64).toNat, 64)] := by
  intro a outside
  apply add_error_frame
  · intro i hi
    exact Body.outside_byte out a 80 i outBound (outside (out.toNat, 80) (by simp)) hi
  · intro i hi
    exact Body.outside_byte (s.regs.rsp.toBitVec + 120#64) a 64 i stageBound
      (outside ((s.regs.rsp.toBitVec + 120#64).toNat, 64) (by simp)) hi

/-- All prologue saves and the return address remain read-only during rejection. -/
theorem add_error_saved_load (s : MachineData) (out : BitVec 64) (v : AddErrorImage)
    (outBound : out.toNat + 80 ≤ 2^64)
    (stackBound : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64)
    (apart : Body.Apart (s.regs.rsp.toBitVec.toNat + 312) 56 out.toNat 80)
    (off count : Nat) (lo : 312 ≤ off) (hi : off + count ≤ 368) :
    Mem.loadInt (addErrorState s out v).dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
  apply memmove_loadInt_congr
  intro i hi'
  apply add_error_frame
  · intro j hj
    unfold Body.Apart at apart
    bv_omega
  · intro j hj
    bv_omega

/-- Every staging write retains its exact private word, not just its footprint. -/
theorem add_error_stage_observed (m : DataMem) (sp : BitVec 64) (v : AddErrorImage)
    (bound : sp.toNat + 224 ≤ 2^64) :
    observe (addErrorStageMem m sp v) sp 120 8 = some v.w0.toNat ∧
    observe (addErrorStageMem m sp v) sp 128 8 = some v.w1.toNat ∧
    observe (addErrorStageMem m sp v) sp 136 8 = some v.w2.toNat ∧
    observe (addErrorStageMem m sp v) sp 144 8 = some v.w3.toNat ∧
    observe (addErrorStageMem m sp v) sp 152 8 = some v.w4.toNat ∧
    observe (addErrorStageMem m sp v) sp 160 8 = some v.w5.toNat ∧
    observe (addErrorStageMem m sp v) sp 168 8 = some v.w6.toNat ∧
    observe (addErrorStageMem m sp v) sp 176 8 = some v.w7.toNat := by
  simp (disch := first | assumption | omega | decide) only
    [observe, addErrorStageMem, error_local_read, load_store_same, Nat.reduceMul]
  simp only [Option.map_some, error_signed_nat, and_self]

end SszX86.BitVector
