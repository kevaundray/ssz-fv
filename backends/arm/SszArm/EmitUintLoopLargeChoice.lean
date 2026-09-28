import SszArm.EmitUintLoopLargePrepare

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

structure LargeRegisters (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (index size : Nat) : Prop where
  count : r (.GPR 8#5) s = BitVec.ofNat 64 words.length
  pointer : r (.GPR 9#5) s = pointer
  bits : r (.GPR 10#5) s = BitVec.ofNat 64 (8 * index)
  index : r (.GPR 11#5) s = BitVec.ofNat 64 index
  length : r (.GPR 1#5) s = BitVec.ofNat 64 size

theorem large_choose {s : ArmState} {args : Args} {width : NatOperand}
    {pointer : BitVec 64} {words : List (BitVec 64)} {size index : Nat}
    (base : BitVec 64) (owned : Owned s args (.uint width) (.uint (.large pointer words)) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1132#64)
    (loop : LargeRegisters s pointer words index size) (inside : index < size)
    (writtenPrefix : Prefix s args (.large pointer words) index) :
    ∃ steps t, run steps s = t ∧ Frame s t args size ∧ read_pc t = base + 1076#64 ∧
      r (.GPR 12#5) t = emittedWord (.large pointer words) index ∧
      LargeRegisters t pointer words index size ∧ Prefix t args (.large pointer words) index := by
  let selected := largeSelected s base
  have selectFrame : Frame s selected args size := largeSelected_frame s base args size
  have selectedOwned := selectFrame.owned owned
  have selectedRegisters := selectFrame.bodyRegisters registers
  have input := owned.operand_at (.large pointer words)
    (by simp [descriptorOperands, valueOperands])
  have physical : pointer.toNat + 8 * words.length ≤ 2^64 := input.2.2.1
  have countBound : words.length < 2^64 := by omega
  have indexBound : index < 2^64 := by have bound := owned.representable; omega
  obtain ⟨indexReg, selectedPC⟩ := largeSelected_data s base index words.length
    indexBound countBound loop.index loop.count
  have selectedLoop : LargeRegisters selected pointer words index size := by
    constructor
    · exact (largeSelected_register s base 8#5 (by decide)).trans loop.count
    · exact (largeSelected_register s base 9#5 (by decide)).trans loop.pointer
    · exact (largeSelected_register s base 10#5 (by decide)).trans loop.bits
    · exact (largeSelected_register s base 11#5 (by decide)).trans loop.index
    · exact (largeSelected_register s base 1#5 (by decide)).trans loop.length
  have selectedPrefix : Prefix selected args (.large pointer words) index := by
    intro prior before
    rw [load_eq_of_mem_eq (largeSelected_memory s base)]
    exact writtenPrefix prior before
  by_cases borrowed : index / 8 < words.length
  · let loaded := largeWordLoaded selected base (words[index / 8]?.getD 0)
    have loadRun : run 9 selected = loaded := large_word_run base selectedOwned selectedRegisters
      (selectFrame.code code) (selectFrame.error.trans error) (selectFrame.aligned aligned)
      (by simpa only [borrowed, ↓reduceIte] using selectedPC)
      selectedLoop.pointer indexReg borrowed
    have loadFrame : Frame selected loaded args size :=
      largeWordLoaded_frame base _ selectedOwned selectedRegisters
    refine ⟨3 + 9, loaded, ?_, selectFrame.trans loadFrame, largeWordLoaded_pc _ _ _, ?_, ?_, ?_⟩
    · rw [run_plus, large_select_run s base code error aligned pc, loadRun]
    · exact largeWordLoaded_word _ _ _
    · constructor
      · exact (largeWordLoaded_register _ _ _ 8#5 (by decide)).trans selectedLoop.count
      · exact (largeWordLoaded_register _ _ _ 9#5 (by decide)).trans selectedLoop.pointer
      · exact (largeWordLoaded_register _ _ _ 10#5 (by decide)).trans selectedLoop.bits
      · exact (largeWordLoaded_register _ _ _ 11#5 (by decide)).trans selectedLoop.index
      · exact (largeWordLoaded_register _ _ _ 1#5 (by decide)).trans selectedLoop.length
    · exact largeWordLoaded_prefix base _ selectedOwned selectedRegisters (by omega) selectedPrefix
  · let loaded := zeroWordLoaded selected base
    have loadRun : run 1 selected = loaded := zero_word_run selected base
      (selectFrame.code code) (selectFrame.error.trans error) (selectFrame.aligned aligned)
      (by simpa only [borrowed, ↓reduceIte] using selectedPC)
    have loadFrame : Frame selected loaded args size := zeroWordLoaded_frame selected base args size
    refine ⟨3 + 1, loaded, ?_, selectFrame.trans loadFrame, zeroWordLoaded_pc _ _, ?_, ?_, ?_⟩
    · rw [run_plus, large_select_run s base code error aligned pc, loadRun]
    · rw [zeroWordLoaded_word]
      simp only [emittedWord, NatOperand.words,
        List.getElem?_eq_none (show words.length ≤ index / 8 by omega), Option.getD_none]
      decide
    · constructor
      · exact (zeroWordLoaded_register _ _ 8#5 (by decide)).trans selectedLoop.count
      · exact (zeroWordLoaded_register _ _ 9#5 (by decide)).trans selectedLoop.pointer
      · exact (zeroWordLoaded_register _ _ 10#5 (by decide)).trans selectedLoop.bits
      · exact (zeroWordLoaded_register _ _ 11#5 (by decide)).trans selectedLoop.index
      · exact (zeroWordLoaded_register _ _ 1#5 (by decide)).trans selectedLoop.length
    · intro prior before
      rw [load_eq_of_mem_eq (zeroWordLoaded_memory selected base)]
      exact selectedPrefix prior before

end SszArm.Emit.Uint
