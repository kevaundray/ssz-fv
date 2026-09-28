import SszArm.EmitUintLoopLarge

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

/-- The Small path terminates at precisely the requested output width; positions
past its sole word write zero, rather than stopping at the operand's byte width. -/
theorem small_loop (remaining : Nat) : ∀ (s : ArmState) (base : BitVec 64) (args : Args)
    (width : NatOperand) (word : BitVec 64) (size index : Nat),
    Owned s args (.uint width) (.uint (.small word)) size → BodyRegisters s args →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 936#64 → SmallRegisters s word index size →
    Prefix s args (.small word) index → index + remaining = size → 0 < remaining →
    ∃ steps t, run steps s = t ∧ Frame s t args size ∧ read_pc t = base + 1000#64 ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size ∧ Prefix t args (.small word) size := by
  induction remaining with
  | zero =>
    intro s base args width word size index owned registers code error aligned pc loop writtenPrefix total positive
    omega
  | succ remaining induction =>
    intro s base args width word size index owned registers code error aligned pc loop writtenPrefix total positive
    have inside : index < size := by omega
    obtain ⟨roundRun, roundFrame, roundLoop, roundPC, roundPrefix⟩ :=
      small_round base owned registers code error aligned pc loop inside writtenPrefix
    by_cases last : remaining = 0
    · have done : index + 1 = size := by omega
      refine ⟨16, smallRound s base, roundRun, roundFrame, ?_, roundLoop.length, ?_⟩
      · simpa only [done, ↓reduceIte] using roundPC
      · simpa only [done] using roundPrefix
    · have more : 0 < remaining := by omega
      have notDone : index + 1 ≠ size := by omega
      obtain ⟨rest, t, restRun, restFrame, finalPC, length, finalPrefix⟩ :=
        induction (smallRound s base) base args width word size (index + 1)
          (roundFrame.owned owned) (roundFrame.bodyRegisters registers)
          (roundFrame.code code) (roundFrame.error.trans error) (roundFrame.aligned aligned)
          (by simpa only [notDone, ↓reduceIte] using roundPC) roundLoop roundPrefix (by omega) more
      refine ⟨16 + rest, t, ?_, roundFrame.trans restFrame, finalPC, length, finalPrefix⟩
      rw [run_plus, roundRun, restRun]

/-- Arbitrarily padded Large operands take the physical limb-load branch only
inside their original backing span. Every later byte follows the zero arm. -/
theorem large_loop (remaining : Nat) : ∀ (s : ArmState) (base : BitVec 64) (args : Args)
    (width : NatOperand) (pointer : BitVec 64) (words : List (BitVec 64)) (size index : Nat),
    Owned s args (.uint width) (.uint (.large pointer words)) size → BodyRegisters s args →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 1132#64 → LargeRegisters s pointer words index size →
    Prefix s args (.large pointer words) index → index + remaining = size → 0 < remaining →
    ∃ steps t, run steps s = t ∧ Frame s t args size ∧ read_pc t = base + 1000#64 ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size ∧ Prefix t args (.large pointer words) size := by
  induction remaining with
  | zero =>
    intro s base args width pointer words size index owned registers code error aligned pc loop writtenPrefix total positive
    omega
  | succ remaining induction =>
    intro s base args width pointer words size index owned registers code error aligned pc loop writtenPrefix total positive
    have inside : index < size := by omega
    obtain ⟨roundSteps, roundState, roundRun, roundFrame, roundLoop, roundPC, roundPrefix⟩ :=
      large_round base owned registers code error aligned pc loop inside writtenPrefix
    by_cases last : remaining = 0
    · have done : index + 1 = size := by omega
      refine ⟨roundSteps, roundState, roundRun, roundFrame, ?_, roundLoop.length, ?_⟩
      · simpa only [done, ↓reduceIte] using roundPC
      · simpa only [done] using roundPrefix
    · have more : 0 < remaining := by omega
      have notDone : index + 1 ≠ size := by omega
      obtain ⟨rest, t, restRun, restFrame, finalPC, length, finalPrefix⟩ :=
        induction roundState base args width pointer words size (index + 1)
          (roundFrame.owned owned) (roundFrame.bodyRegisters registers)
          (roundFrame.code code) (roundFrame.error.trans error) (roundFrame.aligned aligned)
          (by simpa only [notDone, ↓reduceIte] using roundPC) roundLoop roundPrefix (by omega) more
      refine ⟨roundSteps + rest, t, ?_, roundFrame.trans restFrame, finalPC, length, finalPrefix⟩
      rw [run_plus, roundRun, restRun]

end SszArm.Emit.Uint
