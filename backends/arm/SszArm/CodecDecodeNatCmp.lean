import SszArm.CodecDecodeNatCmpEntry

namespace SszArm.Codec.Decode.NatCmpUsize

open SszNative.NatABI

/-- Complete linked `Nat::cmp_usize`, including empty and high-zero-padded Large
representations and numbers larger than 128 bits. Only actual input storage and
sixteen bytes of lowering stack are assumed at the original entry. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (owned : Owned s operand) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand := by
  obtain ⟨fuel, u, executed, frame, ready⟩ := entry_ready s base operand owned code error aligned pc
  have actual : r (.GPR 2#5) u = r (.GPR 2#5) s := frame.registers _ (by decide)
  have link : r (.GPR 30#5) u = r (.GPR 30#5) s := frame.registers _ (by decide)
  have finish (rest : Nat) (t : ArmState) (runTail : run rest u = t)
      (tailFrame : Frame u t) (returned : read_pc t = r (.GPR 30#5) u)
      (value : (r (.GPR 0#5) t).setWidth 8 =
        orderingByte (compare operand.value (r (.GPR 2#5) s).toNat)) :
      ∃ total t, run total s = t ∧ Post s t operand := by
    have whole := frame.trans tailFrame
    refine ⟨fuel + rest, t, ?_, whole, returned.trans link,
      whole.error.trans error, value, ?_⟩
    · rw [run_plus, executed, runTail]
    · exact NatDivision.operand_at_preserved (whole.memoryFrame owned.stackBound)
        operand owned.operandAt owned.operandOwned
  rcases ready with ⟨target, huge⟩ | ⟨target, reconstructed⟩
  · let ops : List Op := [.p72, .p76]
    have follows : Follows base ops u := by
      change r .PC u = _ at target
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, target, BitVec.add_assoc]
    have greater : (r (.GPR 2#5) s).toNat < operand.value := by
      have bound := (r (.GPR 2#5) s).isLt
      omega
    apply finish 2 (block base ops u)
      (block_run base ops u (frame.code code) (frame.error.trans error)
        (frame.aligned aligned) follows)
      (readonly_frame base ops u (by decide))
    · simp [ops, block, Op.effect, put, next, state_simp_rules]
    · simp [ops, block, Op.effect, put, next, state_simp_rules, Nat.compare_eq_gt.mpr greater,
        orderingByte]
  · obtain ⟨rest, t, runTail, tailFrame, returned, value⟩ :=
      return_order u base (frame.code code) (frame.error.trans error) (frame.aligned aligned) target
    exact finish rest t runTail tailFrame returned (by simpa only [reconstructed, actual] using value)

end SszArm.Codec.Decode.NatCmpUsize
