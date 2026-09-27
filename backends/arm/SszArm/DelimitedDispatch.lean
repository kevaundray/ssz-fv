import SszArm.DelimitedBlocks
import SszArm.DelimitedMemory

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem cmp32_zero (a b : BitVec 32) :
    (AddWithCarry a (~~~b) 1#1).2.z = 1#1 ↔ a = b := by
  change (if (AddWithCarry a (~~~b) 1#1).1 = 0#32 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_sub_neg, BitVec.not_not]
  have zero : a - b = 0#32 ↔ a = b := by bv_omega
  simp [zero]

theorem small_fields (s : ArmState) (base : BitVec 64) :
    let t := block base smallOps s
    r (.GPR 20#5) t = 0#64 ∧ r (.GPR 19#5) t = r (.GPR 24#5) s ∧
      t.mem = s.mem ∧ r (.GPR 31#5) t = r (.GPR 31#5) s ∧
      read_pc t = if read_mem_bytes 4 (r (.GPR 1#5) s) s = 1#32
        then base + 364#64 else base + 168#64 := by
  have zero := cmp32_zero (read_mem_bytes 4 (r (.GPR 1#5) s) s) 1#32
  change (AddWithCarry (read_mem_bytes 4 (r (.GPR 1#5) s) s)
    4294967294#32 1#1).2.z = 1#1 ↔ _ at zero
  simp [block, smallOps, Op.effect, put, next, state_simp_rules, zero]

def largeLimitOps : List Op := [.p352, .p356, .p360]

theorem large_limit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 352#64) :
    run 3 s = block base largeLimitOps s := by
  apply block_run base largeLimitOps s hc he ha
  have hpc : r .PC s = base + 352#64 := hp
  simp [largeLimitOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem large_limit_fields (s : ArmState) (base : BitVec 64) :
    let t := block base largeLimitOps s
    t.mem = s.mem ∧ r (.GPR 31#5) t = r (.GPR 31#5) s ∧
      read_pc t = if read_mem_bytes 4 (r (.GPR 1#5) s) s = 1#32
        then base + 364#64 else base + 540#64 := by
  have zero := cmp32_zero (read_mem_bytes 4 (r (.GPR 1#5) s) s) 1#32
  change (AddWithCarry (read_mem_bytes 4 (r (.GPR 1#5) s) s)
    4294967294#32 1#1).2.z = 1#1 ↔ _ at zero
  simp [block, largeLimitOps, Op.effect, put, next, state_simp_rules, zero] <;>
    (split <;> simp_all)

/-- Small count construction has no scratch traffic and retains the full value,
not a comparison against a truncated cap. -/
theorem small_pair (s : ArmState) (base : BitVec 64) (count : Nat)
    (physical : count < 2^64) (low : r (.GPR 24#5) s = BitVec.ofNat 64 count) :
    SszNative.NatMemory.Pair (UintCodec.widthLoad (block base smallOps s))
      (r (.GPR 20#5) (block base smallOps s))
      (r (.GPR 19#5) (block base smallOps s)) count := by
  refine Or.inl ⟨(small_fields s base).1, ?_⟩
  rw [(small_fields s base).2.1, low, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]

end SszArm.Delimited
