import SszArm.NatMulExec
import SszArm.NatMulActivationMemory
import SszArm.NatMulCalls
import SszArm.BitVectorPair
import SszArm.NatFromU128LowerCongruence

namespace SszArm.NatMul

open Delimited (Span MemoryFrame Returned)

def savedRegisters : List (BitVec 5 × Nat) :=
  [(30#5, 0), (28#5, 16), (27#5, 24), (26#5, 32), (25#5, 40),
   (24#5, 48), (23#5, 56), (22#5, 64), (21#5, 72), (20#5, 80), (19#5, 88)]

def saveOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p20, .p24]

def activated (s : ArmState) : ArmState :=
  w (.GPR 31#5) (r (.GPR 31#5) s - 96#64)
    (w .PC (read_pc s + 28#64) (saveMemory s))

theorem save_effect (s : ArmState) (base : BitVec 64) :
    block base saveOps s = activated s := by
  simp [block, saveOps, Op.effect, put, next, activated, saveMemory,
    state_simp_rules, BitVec.add_assoc, NatFromU128.store_field_write]
  rw [w_of_w_commute (fld1 := .PC) (fld2 := .GPR 31#5) (by decide)]
  simp only [state_simp_rules]

theorem save_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 7 s = activated s := by
  rw [← save_effect s base]
  apply block_run base saveOps s code error aligned
  change r .PC s = base at pc
  simp [Follows, saveOps, Op.row, Op.effect, put, next, state_simp_rules,
    pc, BitVec.add_assoc]

structure Saved (entry current : ArmState) : Prop where
  sp : r (.GPR 31#5) current = r (.GPR 31#5) entry - 96#64
  words : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 (r (.GPR 31#5) current + BitVec.ofNat 64 offset) current =
      r (.GPR reg) entry
  x29 : r (.GPR 29#5) current = r (.GPR 29#5) entry
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) entry).setWidth 64

theorem saveMemory_reads (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 96#64 + BitVec.ofNat 64 offset)
      (saveMemory s) = r (.GPR reg) s := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | member | member | member | member | member |
    member | member | member | member | member
  · cases member; exact saveMemory_read_30 s stack
  · cases member; exact saveMemory_read_28 s stack
  · cases member; exact saveMemory_read_27 s stack
  · cases member; exact saveMemory_read_26 s stack
  · cases member; exact saveMemory_read_25 s stack
  · cases member; exact saveMemory_read_24 s stack
  · cases member; exact saveMemory_read_23 s stack
  · cases member; exact saveMemory_read_22 s stack
  · cases member; exact saveMemory_read_21 s stack
  · cases member; exact saveMemory_read_20 s stack
  · cases member; exact saveMemory_read_19 s stack

theorem activated_saved (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    Saved s (activated s) := by
  constructor
  · simp [activated, saveMemory, state_simp_rules]
  · intro reg offset member
    simpa [activated, state_simp_rules] using saveMemory_reads s stack reg offset member
  · simp [activated, saveMemory, state_simp_rules]
  · intro reg low high
    simp [activated, saveMemory, state_simp_rules]

end SszArm.NatMul
