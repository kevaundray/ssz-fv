import SszArm.MeasureBitsConstructorContract

namespace SszArm.Measure.Bits.Constructor

open UintCodec (widthLoad)

theorem return_executes (s u : ArmState) (base : BitVec 64)
    (space : Space s) (code : CodeAt u base) (error : read_err u = .None)
    (aligned : CheckSPAlignment u) (pc : read_pc u = base + 1916#64)
    (native : NatFromU128.Post (Helpers.called .constructWidth s base) u) :
    ∃ fuel t, run fuel u = t ∧ ReturnedPost u t base (result s) (tailWrites s) := by
  have output : r (.GPR 19#5) u = r (.GPR 19#5) s :=
    (native.returned.registers 19#5 (by decide) (by decide)).trans
      (Helpers.called_register _ _ _ _ (by decide))
  have stack : r (.GPR 31#5) u = r (.GPR 31#5) s :=
    native.returned.sp.trans (Helpers.called_register _ _ _ _ (by decide))
  have scratchRegister : r (.GPR 23#5) u = r (.GPR 31#5) u + 120#64 := by
    rw [native.returned.registers 23#5 (by decide) (by decide),
      Helpers.called_register _ _ _ _ (by decide), stack]
    exact space.savedScratch
  have scratchNat : (r (.GPR 31#5) s + 120#64).toNat = (r (.GPR 31#5) s).toNat + 120 := by
    have := space.scratchBound
    bv_omega
  have observed : SszNative.NatArithmetic.AddResultAt (widthLoad u)
      ((r (.GPR 31#5) u).toNat + 120) (NatFromU128.outcome s).result := by
    have input := native.result
    simpa only [Helpers.constructor_called_outcome,
      Helpers.called_register .constructWidth s base 0#5 (by decide),
      space.scratch, scratchNat, stack] using input
  have storage : (NatDivision.arenaOf s).base + (NatDivision.arenaOf s).capacity ≤ 2^64 :=
    space.native.storage
  cases checked : (NatFromU128.outcome s).result with
  | ok operand =>
    have uSpace : Result.SuccessSpace u := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [stack] using space.success.stack
      · simpa only [output] using space.success.bound
      · simpa only [output, stack] using space.success.fields
      · simpa only [output, stack] using space.success.status
    have sameWrites : Result.successWrites u = Result.successWrites s := by
      simp only [Result.successWrites, output, stack]
    have borrowed : NatDivision.OperandOwned (Result.successWrites u) operand := by
      rw [sameWrites]
      apply Helpers.fromWide_result_owned (Result.successWrites s) (NatDivision.arenaOf s)
        (NatFromU128.wide s) storage
      · simpa only [tailWrites, checked] using space.freeTail
      · exact checked
    obtain ⟨t, executed, post⟩ := returned_success_executes u base code error aligned pc uSpace
      operand (by simpa only [checked] using observed) borrowed
    refine ⟨36, t, executed, ?_⟩
    simpa only [result, checked, Except.mapError, tailWrites, sameWrites] using post
  | error reason =>
    have failure : reason = .scratchExhausted := Helpers.fromWide_failure_scratch
      (NatDivision.arenaOf s) (NatFromU128.wide s) reason checked
    subst reason
    have originalSpace : Propagation.CopySpace s := by simpa only [checked] using space.failure
    have uSpace : Propagation.CopySpace u := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [output] using originalSpace.output
      · simpa only [stack] using originalSpace.scratch
      · simpa only [output, stack] using originalSpace.separate
    obtain ⟨t, executed, post⟩ := returned_error_executes u base code error aligned pc scratchRegister
      uSpace (by simpa only [checked, SszNative.NatArithmetic.AddResultAt] using observed)
    refine ⟨3 + (3 + (Memcpy.fuel 48 + 1) + 4), t, executed, ?_⟩
    simpa only [result, checked, Except.mapError, tailWrites, output] using post

end SszArm.Measure.Bits.Constructor
