import SszArm.EmitUintWidthLow

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open SszNative.Limbs

theorem scan_width (s : ArmState) (base : BitVec 64) (args : Args)
    (pointer : BitVec 64) (words : List (BitVec 64)) (number : NatOperand) (size : Nat)
    (owned : Owned s args (.uint (.large pointer words)) (.uint number) size)
    (registers : BodyRegisters s args) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 80#64) (address : r (.GPR 8#5) s = pointer)
    (count : r (.GPR 1#5) s = BitVec.ofNat 64 words.length)
    (index : r (.GPR 10#5) s = BitVec.ofNat 64 words.length - 1#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t args size ∧
      (read_pc t = base + 904#64 ∨ read_pc t = base + 1000#64 ∧ size = 0) ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size := by
  have source := operand_source owned registers pointer words (by simp)
  have stored := operand_words owned pointer words (by simp)
  have lenBound : words.length < 2^64 := by have bound := source.2.1; omega
  have significant : sigWords words ≤ 1 := width_fits_word owned
  obtain ⟨fuel, u, runScan, narrow, pointerU, pcU, indexU⟩ :=
    significant_scan base pointer words words.length s (Nat.le_refl _)
      code error aligned pc address index source stored
  have frame : Frame s u args size := narrow_frame owned registers narrow
  have ownedU := frame.owned owned
  have regsU := frame.bodyRegisters registers
  have codeU := frame.code code
  have errorU := frame.error.trans error
  have alignedU := frame.aligned aligned
  have countU : r (.GPR 1#5) u = BitVec.ofNat 64 words.length :=
    (narrow.registers _ (by decide)).trans count
  change read_pc u = base + BitVec.ofNat 64 (if sigWords words = 0 then 896 else 132) at pcU
  change sigWords words ≠ 0 → r (.GPR 9#5) u = BitVec.ofNat 64 (sigWords words - 1) at indexU
  by_cases zero : sigWords words = 0
  · have upc : read_pc u = base + 896#64 := by simpa [zero] using pcU
    by_cases empty : words.length = 0
    · have wordsNil : words = [] := List.length_eq_zero_iff.mp empty
      have sizeZero : size = 0 := by
        have expected := expected_width owned
        simpa [wordsNil, NatOperand.value, NatOperand.words, value] using expected.symm
      let t := widthBlock base [.p896] u
      have runTail : run 1 u = t := width_run base [.p896] u codeU errorU alignedU ⟨upc, trivial⟩
      have tailFrame : Frame u t args size := width_readonly_frame base [.p896] u args size (by decide)
      refine ⟨fuel + 1, t, ?_, frame.trans tailFrame, Or.inr ⟨?_, sizeZero⟩, ?_⟩
      · rw [run_plus, runScan, runTail]
      · simp [t, widthBlock, WidthOp.effect, state_simp_rules, countU, empty]
      · simp [t, widthBlock, WidthOp.effect, state_simp_rules, countU, empty, sizeZero]
    · have nonempty : 0 < words.length := by omega
      have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      let v := widthBlock base [.p896] u
      have runTail : run 1 u = v := width_run base [.p896] u codeU errorU alignedU ⟨upc, trivial⟩
      have tailFrame : Frame u v args size := width_readonly_frame base [.p896] u args size (by decide)
      have pcV : read_pc v = base + 900#64 := by
        simp [v, widthBlock, WidthOp.effect, state_simp_rules, countU, countNonzero]
      have ptrV : r (.GPR 8#5) v = pointer := by
        simpa [v, widthBlock, WidthOp.effect, state_simp_rules] using pointerU
      obtain ⟨t, runLoad, loadFrame, pcT, valueT⟩ := load_width v base args pointer words number size
        (tailFrame.owned ownedU) (tailFrame.bodyRegisters regsU) (tailFrame.code codeU)
        (tailFrame.error.trans errorU) (tailFrame.aligned alignedU) pcV ptrV nonempty
      refine ⟨fuel + 1 + 1, t, ?_, (frame.trans tailFrame).trans loadFrame, Or.inl pcT, valueT⟩
      rw [run_plus, run_plus, runScan, runTail, runLoad]
  · have one : sigWords words = 1 := by omega
    have nonempty : 0 < words.length := by have := sigWords_le_length words; omega
    have upc : read_pc u = base + 132#64 := by simpa [zero] using pcU
    have indexZero : r (.GPR 9#5) u = 0#64 := by simpa [one] using indexU zero
    let ops : List WidthOp := [.p132, .p136, .p140]
    let v := widthBlock base ops u
    have follows : WidthFollows base ops u := by
      change r .PC u = base + 132#64 at upc
      simp (config := {decide := true, instances := true})
        [ops, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Dispatch.next,
         Dispatch.compare64, state_simp_rules, bitvec_rules, minimal_theory,
         upc, indexZero, BitVec.add_assoc]
    have runTail : run 3 u = v := width_run base ops u codeU errorU alignedU follows
    have tailFrame : Frame u v args size := width_readonly_frame base ops u args size (by decide)
    have pcV : read_pc v = base + 900#64 := by
      simp (config := {decide := true, instances := true})
        [v, ops, widthBlock, WidthOp.effect, put, next, Dispatch.next,
         Dispatch.compare64, state_simp_rules, bitvec_rules, minimal_theory, indexZero]
    have ptrV : r (.GPR 8#5) v = pointer := by
      simpa [v, ops, widthBlock, WidthOp.effect, put, next, Dispatch.next,
        Dispatch.compare64, state_simp_rules] using pointerU
    obtain ⟨t, runLoad, loadFrame, pcT, valueT⟩ := load_width v base args pointer words number size
      (tailFrame.owned ownedU) (tailFrame.bodyRegisters regsU) (tailFrame.code codeU)
      (tailFrame.error.trans errorU) (tailFrame.aligned alignedU) pcV ptrV nonempty
    refine ⟨fuel + 3 + 1, t, ?_, (frame.trans tailFrame).trans loadFrame, Or.inl pcT, valueT⟩
    rw [run_plus, run_plus, runScan, runTail, runLoad]

end SszArm.Emit.Uint
