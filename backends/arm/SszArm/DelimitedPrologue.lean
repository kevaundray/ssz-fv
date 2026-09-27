import SszArm.DelimitedActivation
import SszArm.UintResultMemory

namespace SszArm.Delimited

open BoolCodec
open UintCodec.Tail

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

macro "prologue_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [block, prologueOps, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

/-- The activation stores and the last-byte lowering save stay inside exactly
the nonempty 112-byte writable activation, not an invented enlarged frame. -/
theorem prologue_frame (s : ArmState) (base : BitVec 64)
    (stack : 112 ≤ (r (.GPR 31#5) s).toNat)
    (nonempty : r (.GPR 3#5) s ≠ 0#64) :
    MemoryFrame (localWrites s) s (block base prologueOps s) := by
  intro a ha
  have outside := ha (activationSpan s) (by simp [localWrites])
  simp only [activationSpan, nonempty, ↓reduceIte, Prod.fst, Prod.snd] at outside
  prologue_expand
  simp (disch := tail_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem prologue_saved (s : ArmState) (base : BitVec 64)
    (stack : 112 ≤ (r (.GPR 31#5) s).toNat) :
    Saved s (block base prologueOps s) := by
  constructor
  · prologue_expand
    bv_omega
  · intro reg offset member
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      prologue_expand
      tail_reads
  · intro reg low high
    simp [block, prologueOps, Op.effect, put, next, state_simp_rules]

/-- The byte loaded by the prologue is observable in the final prologue memory,
since no stores follow that load. This allows caller ownership to transfer the
byte independently of the instruction proof. -/
theorem prologue_loaded (s : ArmState) (base : BitVec 64) :
    let t := block base prologueOps s
    r (.GPR 8#5) t =
      (read_mem_bytes 1 (r (.GPR 2#5) s + (r (.GPR 3#5) s - 1#64)) t).setWidth 64 := by
  dsimp only
  prologue_expand

theorem prologue_arguments (s : ArmState) (base : BitVec 64) :
    let t := block base prologueOps s
    (∀ reg : BitVec 5, reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5] → r (.GPR reg) t = r (.GPR reg) s) ∧
      r (.GPR 25#5) t = r (.GPR 3#5) s - 1#64 := by
  constructor
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> prologue_expand
  · prologue_expand

theorem prologue_pc (s : ArmState) (base : BitVec 64) :
    let t := block base prologueOps s
    read_pc t = if (r (.GPR 8#5) t).setWidth 32 = 0#32
      then base + 184#64 else base + 64#64 := by
  dsimp only
  prologue_expand

/-- The actual entry CBZ selects the save/load path only for a nonempty slice. -/
theorem nonempty_entry (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry)
    (nonempty : r (.GPR 3#5) s ≠ 0#64) :
    let u := Op.p0.effect base s
    run 16 s = block base prologueOps u := by
  have first : stepi s = Op.p0.effect base s :=
    step s base .p0 hc (by simpa [entry, Op.row] using hp) he ha
  rw [show 16 = 15 + 1 by decide, run, first]
  apply prologue_run
  · simpa only [CodeAt, Op.program] using hc
  · simpa only [Op.error] using he
  · exact Op.aligned .p0 base s ha
  · simp [Op.effect, nonempty, state_simp_rules]

end SszArm.Delimited
