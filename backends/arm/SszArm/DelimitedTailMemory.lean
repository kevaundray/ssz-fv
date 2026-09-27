import SszArm.DelimitedActivation
import SszArm.DelimitedZeroMemory

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The epilogue reads six saved pairs and performs only the final tag store. -/
theorem epilogue_memory (s : ArmState) (base : BitVec 64) :
    (block base epilogueOps s).mem =
      (write_mem_bytes 8 (r (.GPR 0#5) s) (r (.GPR 8#5) s) s).mem := by
  simp [block, epilogueOps, Op.effect, put, next, state_simp_rules]
  apply mem_write_mem_bytes_of_mem_eq
  simp [ArmState.mem_w_eq_mem]

theorem epilogue_load (s : ArmState) (base : BitVec 64) (address bytes : Nat) :
    widthLoad (block base epilogueOps s) address bytes =
      widthLoad (write_mem_bytes 8 (r (.GPR 0#5) s) (r (.GPR 8#5) s) s) address bytes := by
  unfold widthLoad
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (epilogue_memory s base)) bytes]

def tailWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 76), ((r (.GPR 31#5) s).toNat - 16, 16)]

structure TailOwned (s : ArmState) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 96 ≤ 2^64
  output : (r (.GPR 0#5) s).toNat + 76 ≤ 2^64
  working : (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  activation : (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 31#5) s).toNat ∨
    (r (.GPR 31#5) s).toNat + 96 ≤ (r (.GPR 0#5) s).toNat

theorem saved_register_bound (reg : BitVec 5) (offset : Nat)
    (member : (reg, offset) ∈ savedRegisters) : offset + 8 ≤ 96 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> omega

/-- Every saved activation word survives a statically disjoint memory frame.
No caller-owned readonly span is required to be disjoint from another readonly
span, and vector preservation observes only the ABI callee-saved lanes. -/
theorem Saved.frame {entry s t : ArmState} {writes : List Span}
    (saved : Saved entry s) (frame : MemoryFrame writes s t)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (physical : (r (.GPR 31#5) s).toNat + 96 ≤ 2^64)
    (owned : Protected writes (r (.GPR 31#5) s).toNat 96)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) : Saved entry t := by
  refine ⟨sp.trans saved.sp, ?_, ?_⟩
  · intro reg offset member
    have bound := saved_register_bound reg offset member
    have wordOwned : Protected writes ((r (.GPR 31#5) s).toNat + offset) 8 := by
      right
      intro span inWrites
      rcases owned with empty | separate
      · omega
      · have hsep := separate span inWrites
        omega
    have same := frame.load ((r (.GPR 31#5) s).toNat + offset) 8 (by omega) wordOwned
    have sameNat := Option.some.inj same
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at sameNat
    rw [sp, BitVec.eq_of_toNat_eq sameNat]
    exact saved.words reg offset member
  · intro reg low high
    exact (vectors reg low high).trans (saved.vectors reg low high)

theorem TailOwned.activation_protected {s : ArmState} (owned : TailOwned s) :
    Protected (tailWrites s) (r (.GPR 31#5) s).toNat 96 := by
  right
  intro span member
  simp only [tailWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact owned.activation.symm
  · simp only [Prod.fst, Prod.snd]
    have low := owned.stackLow
    omega

end SszArm.Delimited
