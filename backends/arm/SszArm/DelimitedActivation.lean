import SszArm.DelimitedBlocks
import SszArm.DelimitedMemory

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The actual six STP save pairs, at their nonempty activation offsets. -/
def savedRegisters : List (BitVec 5 × Nat) :=
  [(29#5, 0), (30#5, 8), (28#5, 16), (27#5, 24),
   (26#5, 32), (25#5, 40), (24#5, 48), (23#5, 56),
   (22#5, 64), (21#5, 72), (20#5, 80), (19#5, 88)]

/-- The epilogue needs only the current saved-word observations, not a giant
unfolded state containing the entire decode execution. -/
structure Saved (entry current : ArmState) : Prop where
  sp : r (.GPR 31#5) current = r (.GPR 31#5) entry - 96#64
  words : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 (r (.GPR 31#5) current + BitVec.ofNat 64 offset) current =
      r (.GPR reg) entry
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) entry).setWidth 64

theorem epilogue_restores (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) (error : read_err s = .None) :
    Returned entry (block base epilogueOps s) := by
  have h29 := saved.words 29#5 0 (by decide)
  have h30 := saved.words 30#5 8 (by decide)
  have h28 := saved.words 28#5 16 (by decide)
  have h27 := saved.words 27#5 24 (by decide)
  have h26 := saved.words 26#5 32 (by decide)
  have h25 := saved.words 25#5 40 (by decide)
  have h24 := saved.words 24#5 48 (by decide)
  have h23 := saved.words 23#5 56 (by decide)
  have h22 := saved.words 22#5 64 (by decide)
  have h21 := saved.words 21#5 72 (by decide)
  have h20 := saved.words 20#5 80 (by decide)
  have h19 := saved.words 19#5 88 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h29 h30 h28 h27 h26 h25 h24 h23 h22 h21 h20 h19
  constructor
  · simpa [block, epilogueOps, Op.effect, put, next, state_simp_rules,
      BitVec.add_assoc, h30]
  · exact (block_error _ _ _).trans error
  · simp [block, epilogueOps, Op.effect, put, next, state_simp_rules,
      saved.sp, BitVec.sub_add_cancel]
  · intro reg low high
    have members : reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨
        reg = 27#5 ∨ reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by bv_omega
    rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [block, epilogueOps, Op.effect, put, next, state_simp_rules,
        BitVec.add_assoc, h29, h30, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19]
  · intro reg low high
    simpa [block, epilogueOps, Op.effect, put, next, state_simp_rules] using
      saved.vectors reg low high

/-- Executing the real epilogue includes its final output tag store and RET. -/
theorem epilogue_return (entry s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 980#64) (saved : Saved entry s) :
    ∃ t, run 8 s = t ∧ Returned entry t :=
  ⟨block base epilogueOps s, epilogue_run s base hc he ha hp,
    epilogue_restores entry s base saved he⟩

end SszArm.Delimited
