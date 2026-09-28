import SszArm.BitVectorStageState
import SszArm.BitVectorLeafOwned

namespace SszArm.BitVector

open UintCodec (widthLoad)

theorem preparation_observe (phase : Stages.CallPreparation) (c : ArmState) (base : BitVec 64) :
    widthLoad (phase.result c base) = widthLoad c := by
  funext address bytes
  cases phase <;> simp only [widthLoad, Stages.CallPreparation.result, state_simp_rules]

theorem call_observe (site : CallSite) (c : ArmState) (base : BitVec 64) :
    widthLoad (called site c base) = widthLoad c := by
  funext address bytes
  simp only [widthLoad, called, state_simp_rules]

theorem exact_writes_local (c : ArmState) (expected : SszNative.NatOperand) :
    Covers (NatExact.localWrites c) (NatExact.writesFor c expected) := by
  intro span member
  simp only [NatExact.writesFor, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨((r (.GPR 0#5) c).toNat, 68), by simp [NatExact.localWrites], ?_, ?_⟩
    all_goals split <;> simp only [Prod.fst, Prod.snd] <;> omega
  · exact ⟨((r (.GPR 31#5) c).toNat - 16, 16), by simp [NatExact.localWrites],
      Nat.le_refl _, Nat.le_refl _⟩

theorem narrow_writes_local (c : ArmState) (length : SszNative.NatOperand) :
    Covers (NatToU128.localWrites c) (NatToU128.writesFor c length) := by
  intro span member
  simp only [NatToU128.writesFor, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨((r (.GPR 0#5) c).toNat, 32), by simp [NatToU128.localWrites], Nat.le_refl _, ?_⟩
    simp only [Prod.fst, Prod.snd]
    split <;> omega
  · exact ⟨((r (.GPR 31#5) c).toNat - 16, 16), by simp [NatToU128.localWrites],
      Nat.le_refl _, Nat.le_refl _⟩

end SszArm.BitVector
