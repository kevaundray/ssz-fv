import SszArm.EmitUintWidthNormalize

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

theorem width_normalize (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : NatOperand) (size : Nat)
    (code : CodeAt s base) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 60#64)
    (descriptor : r (.GPR 1#5) s = args.descriptor) (tag : r (.GPR 9#5) s = 1#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t args size ∧
      (read_pc t = base + 904#64 ∨ read_pc t = base + 1000#64 ∧ size = 0) ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size := by
  let u := widthHeader base s
  have runHeader : run 4 s = u := header_run s base code error aligned pc tag
  have frame : Frame s u args size := header_frame s base args size
  have pair := header_pair s base args width number size owned descriptor
  have pcU := header_pc s base args width number size owned descriptor
  change r (.GPR 8#5) u = width.pointer ∧ r (.GPR 1#5) u = width.payload at pair
  change read_pc u = base + (if width.pointer = 0#64 then 904#64 else 76#64) at pcU
  cases width with
  | small word =>
    have value : word.toNat = size := by
      simpa [NatOperand.value, NatOperand.words, SszNative.Limbs.value] using expected_width owned
    refine ⟨4, u, runHeader, frame, Or.inl ?_, ?_⟩
    · simpa [NatOperand.pointer] using pcU
    · simpa [NatOperand.payload, ← value] using pair.2
  | large pointer words =>
    have input := owned.operand_at (.large pointer words) (by simp [descriptorOperands, valueOperands])
    have positive : pointer ≠ 0#64 := by
      intro zero
      have nonzero := input.1
      simp [zero] at nonzero
    have upc : read_pc u = base + 76#64 := by simpa [NatOperand.pointer, positive] using pcU
    let v := widthBlock base [.p76] u
    have runInit : run 1 u = v := width_run base [.p76] u (frame.code code)
      (frame.error.trans error) (frame.aligned aligned) ⟨upc, trivial⟩
    have initFrame : Frame u v args size := width_readonly_frame base [.p76] u args size (by decide)
    have fullFrame := frame.trans initFrame
    have pcV : read_pc v = base + 80#64 := by
      change r .PC u = base + 76#64 at upc
      simp [v, widthBlock, WidthOp.effect, put, next, Dispatch.next, state_simp_rules,
        upc, BitVec.add_assoc]
    have ptrV : r (.GPR 8#5) v = pointer := by
      simpa [v, widthBlock, WidthOp.effect, put, next, Dispatch.next, state_simp_rules,
        NatOperand.pointer] using pair.1
    have countV : r (.GPR 1#5) v = BitVec.ofNat 64 words.length := by
      simpa [v, widthBlock, WidthOp.effect, put, next, Dispatch.next, state_simp_rules,
        NatOperand.payload] using pair.2
    have indexV : r (.GPR 10#5) v = BitVec.ofNat 64 words.length - 1#64 := by
      simp [v, widthBlock, WidthOp.effect, put, next, Dispatch.next, state_simp_rules,
        pair.2, NatOperand.payload]
    obtain ⟨fuel, t, runScan, scanFrame, exit, value⟩ := scan_width v base args pointer words number size
      (fullFrame.owned owned) (fullFrame.bodyRegisters registers) (fullFrame.code code)
      (fullFrame.error.trans error) (fullFrame.aligned aligned) pcV ptrV countV indexV
    refine ⟨4 + 1 + fuel, t, ?_, fullFrame.trans scanFrame, exit, value⟩
    rw [run_plus, run_plus, runHeader, runInit, runScan]

end SszArm.Emit.Uint
