import SszArm.NatDivisionExec
import SszArm.NatDivisionContract
import SszArm.UintResultMemory

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame Returned)
open BoolCodec
open UintCodec.Tail

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def prologueOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p20, .p24, .p28]

def savedRegisters : List (BitVec 5 × Nat) :=
  [(30#5, 0), (24#5, 16), (23#5, 24), (22#5, 32),
   (21#5, 40), (20#5, 48), (19#5, 56)]

/-- Saved words refer to the original entry registers, not the registers after
one of the five BL instructions has replaced LR. -/
structure Saved (original current : ArmState) : Prop where
  sp : r (.GPR 31#5) current = r (.GPR 31#5) original - 64#64
  words : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 (r (.GPR 31#5) current + BitVec.ofNat 64 offset) current =
      r (.GPR reg) original
  high : ∀ reg : BitVec 5, 25 ≤ reg.toNat → reg.toNat ≤ 29 →
    r (.GPR reg) current = r (.GPR reg) original
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) original).setWidth 64

macro "division_prologue_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [block, prologueOps, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) :
    run 8 s = block base prologueOps s := by
  apply block_run base prologueOps s hc he ha
  have hpc : r .PC s = base := hp
  simp (config := {decide := true, instances := true})
    [prologueOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

theorem prologue_pc (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base) :
    read_pc (block base prologueOps s) = base + 32#64 := by
  have hpc : r .PC s = base := hp
  simp [block, prologueOps, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem prologue_frame (s : ArmState) (base : BitVec 64)
    (stack : 80 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 64, 64)] s
      (block base prologueOps s) := by
  intro a ha
  have outside := ha ((r (.GPR 31#5) s).toNat - 64, 64) (by simp)
  simp only [Prod.fst, Prod.snd] at outside
  division_prologue_expand
  simp (disch := tail_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem prologue_saved (s : ArmState) (base : BitVec 64)
    (stack : 80 ≤ (r (.GPR 31#5) s).toNat) :
    Saved s (block base prologueOps s) := by
  constructor
  · division_prologue_expand
  · intro reg offset member
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      division_prologue_expand
      tail_reads
  · intro reg low high
    have other : reg ≠ 19#5 ∧ reg ≠ 20#5 ∧ reg ≠ 21#5 ∧ reg ≠ 31#5 := by bv_omega
    simp [block, prologueOps, Op.effect, put, next, state_simp_rules,
      other.1, other.2.1, other.2.2.1, other.2.2.2]
  · intro reg low high
    simp [block, prologueOps, Op.effect, put, next, state_simp_rules]

theorem prologue_arguments (s : ArmState) (base : BitVec 64) :
    let t := block base prologueOps s
    (∀ reg : BitVec 5, reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5] → r (.GPR reg) t = r (.GPR reg) s) ∧
      r (.GPR 19#5) t = r (.GPR 0#5) s ∧
      r (.GPR 20#5) t = r (.GPR 3#5) s ∧
      r (.GPR 21#5) t = r (.GPR 4#5) s := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> division_prologue_expand
  all_goals division_prologue_expand

/-- Body blocks may overwrite their 16-byte lowering slots, but not the saved
activation. This transports all seven saved words across such a physical frame. -/
theorem Saved.preserve {original s t : ArmState} {writes : List Span}
    (saved : Saved original s) (stack : 80 ≤ (r (.GPR 31#5) original).toNat)
    (frame : MemoryFrame writes s t)
    (activationOwned : Protected writes ((r (.GPR 31#5) original).toNat - 64) 64)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (high : ∀ reg : BitVec 5, 25 ≤ reg.toNat → reg.toNat ≤ 29 →
      r (.GPR reg) t = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Saved original t := by
  refine ⟨sp.trans saved.sp, ?_, ?_, ?_⟩
  · intro reg offset member
    have range : offset + 8 ≤ 64 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have address : (r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat =
        (r (.GPR 31#5) original).toNat - 64 + offset := by
      rw [saved.sp]
      bv_omega
    rw [sp, frame.read _ 8 (by rw [address]; omega)]
    · exact saved.words reg offset member
    · rw [address]
      exact activationOwned.subspan offset 8 range
  · intro reg low hi
    exact (high reg low hi).trans (saved.high reg low hi)
  · intro reg low hi
    exact (vectors reg low hi).trans (saved.vectors reg low hi)

end SszArm.NatDivision
