import SszArm.DelimitedBlocks
import SszArm.DelimitedArenaArithmetic
import SszArm.UintWidthMemory

namespace SszArm.Delimited

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive ArenaCheckKind where
  | address | rounding | alignment | ending | capacity
  deriving DecidableEq

def ArenaCheckKind.ops : ArenaCheckKind → List Op
  | .address => arenaAddressOps
  | .rounding => arenaRoundOps
  | .alignment => arenaAlignOps
  | .ending => arenaEndOps
  | .capacity => arenaCapacityOps

/-- None of the checked-overflow branches commits memory or touches a saved
register. This interface is independent of which guard ultimately fails. -/
theorem arena_check_frame (kind : ArenaCheckKind) (s : ArmState) (base : BitVec 64) :
    WidthFrame s (block base kind.ops s) ∧ (block base kind.ops s).mem = s.mem := by
  constructor
  · constructor
    · exact block_program _ _ _
    · exact block_error _ _ _
    · intro reg notChanged
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notChanged
      cases kind <;> simp (disch := simp_all)
        [ArenaCheckKind.ops, arenaAddressOps, arenaRoundOps, arenaAlignOps,
         arenaEndOps, arenaCapacityOps, block, Op.effect, put, next, state_simp_rules]
    · intro reg
      cases kind <;> simp [ArenaCheckKind.ops, arenaAddressOps, arenaRoundOps, arenaAlignOps,
        arenaEndOps, arenaCapacityOps, block, Op.effect, put, next, state_simp_rules]
    · intro a outside
      cases kind <;> simp [ArenaCheckKind.ops, arenaAddressOps, arenaRoundOps, arenaAlignOps,
        arenaEndOps, arenaCapacityOps, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> simp [ArenaCheckKind.ops, arenaAddressOps, arenaRoundOps, arenaAlignOps,
      arenaEndOps, arenaCapacityOps, block, Op.effect, put, next, state_simp_rules]

private theorem cmp_hi (a b : BitVec 64) :
    ((AddWithCarry a (~~~b) 1#1).2.c = 1#1 ∧
      (AddWithCarry a (~~~b) 1#1).2.z ≠ 1#1) ↔ b.toNat < a.toNat := by
  have zero : (AddWithCarry a (~~~b) 1#1).2.z ≠ 1#1 ↔
      (AddWithCarry a (~~~b) 1#1).2.z = 0#1 := by bv_omega
  rw [zero]
  exact Udivti3.cmp_high a b

theorem arena_address_exit (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 4#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s
    let t := block base arenaAddressOps s
    r (.GPR 8#5) t = pointer ∧ r (.GPR 9#5) t = used ∧
      r (.GPR 10#5) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 752#64 else base + 284#64 := by
  simp [block, arenaAddressOps, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_round_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base arenaRoundOps s) =
      if 2^64 < (r (.GPR 10#5) s).toNat + 8 then base + 752#64 else base + 292#64 := by
  simp [block, arenaRoundOps, Op.effect, put, next, state_simp_rules, cmn_hi]

theorem arena_align_exit (s : ArmState) (base : BitVec 64) :
    let aligned := (r (.GPR 10#5) s + 7#64) &&& 18446744073709551608#64
    let padding := aligned - r (.GPR 10#5) s
    let t := block base arenaAlignOps s
    r (.GPR 11#5) t = aligned ∧ r (.GPR 10#5) t = padding ∧
      r (.GPR 9#5) t = padding + r (.GPR 9#5) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 9#5) s).toNat
        then base + 752#64 else base + 312#64 := by
  simp [block, arenaAlignOps, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_end_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base arenaEndOps s) =
      if 2^64 < (r (.GPR 9#5) s).toNat + 17 then base + 752#64 else base + 320#64 := by
  simp [block, arenaEndOps, Op.effect, put, next, state_simp_rules, cmn_hi]

theorem arena_capacity_exit (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
    let finish := r (.GPR 9#5) s + 16#64
    let t := block base arenaCapacityOps s
    r (.GPR 11#5) t = capacity ∧ r (.GPR 10#5) t = finish ∧
      read_pc t = if capacity.toNat < finish.toNat then base + 752#64 else base + 336#64 := by
  simp [block, arenaCapacityOps, Op.effect, put, next, state_simp_rules, cmp_hi]

end SszArm.Delimited
