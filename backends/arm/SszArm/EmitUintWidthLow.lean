import SszArm.EmitUintWidthEntry
import SszArm.EmitUintScan

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open SszNative.Limbs

theorem low_word_of_representable (words : List (BitVec 64))
    (bound : value words < 2^64) : words[0]?.getD 0#64 = BitVec.ofNat 64 (value words) := by
  cases words with
  | nil => rfl
  | cons first rest =>
    have restZero : value rest = 0 := by
      simp only [value] at bound
      omega
    simp [value, restZero]

theorem load_width (s : ArmState) (base : BitVec 64) (args : Args)
    (pointer : BitVec 64) (words : List (BitVec 64)) (number : NatOperand) (size : Nat)
    (owned : Owned s args (.uint (.large pointer words)) (.uint number) size)
    (registers : BodyRegisters s args) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 900#64) (address : r (.GPR 8#5) s = pointer)
    (nonempty : 0 < words.length) :
    ∃ t, run 1 s = t ∧ Frame s t args size ∧
      read_pc t = base + 904#64 ∧ r (.GPR 1#5) t = BitVec.ofNat 64 size := by
  have wordsAt := operand_words owned pointer words (by simp)
  have word := wordsAt ⟨0, nonempty⟩
  have expected := expected_width owned
  have bound : value words < 2^64 := by
    change value words = size at expected
    rw [expected]
    exact owned.representable
  have low : read_mem_bytes 8 pointer s = BitVec.ofNat 64 size := by
    have low' : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
      simpa [List.getElem?_eq_getElem nonempty] using word
    rw [low', low_word_of_representable words bound]
    exact congrArg (BitVec.ofNat 64) expected
  let t := widthBlock base [.p900] s
  have follows : WidthFollows base [.p900] s := ⟨pc, trivial⟩
  refine ⟨t, width_run base [.p900] s code error aligned follows,
    width_readonly_frame base [.p900] s args size (by decide), ?_, ?_⟩
  · change r .PC s = base + 900#64 at pc
    simp [t, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules, pc, BitVec.add_assoc]
  · simp [t, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules, address, low]

end SszArm.Emit.Uint
