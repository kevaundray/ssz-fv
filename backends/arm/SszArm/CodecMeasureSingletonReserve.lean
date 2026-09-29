import SszArm.CodecMeasureSingletonGuards
import SszCodecMeasure

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

def ChecksPost (s t : ArmState) (base address capacity used : BitVec 64) : Prop :=
  Checkpoint s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 5 = none ∧
        read_pc t = base + 168#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 5 ∧
        read_pc t = base + 84#64 ∧ r (.GPR 8) t = address ∧
        (r (.GPR 9) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR 10) t).toNat = SszNative.Arena.finish address.toNat used.toNat 5))

private theorem checks_failure (s t : ArmState) (base address capacity used : BitVec 64)
    (reached : Checkpoint s t) (pc : read_pc t = base + 168#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 5) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used := by
  obtain ⟨fuel, runs⟩ := reached.runs
  exact ⟨fuel, t, runs, reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ 5 (by decide)).2 failed, pc⟩⟩

/-- All five guards execute with their actual linked branch displacements.
Invalid cursors and every checked-add failure reach the native error block
without any write; success stops immediately before pointer/commit stores. -/
theorem checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 12#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 1) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 1) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 1) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used := by
  let a := block Guard.address.ops s
  have ra : Checkpoint s a := (Checkpoint.refl s).step .address base code error pc
  have ea := address_exit s base pc
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 32#64 := ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 10) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block Guard.round.ops a
    have rb : Checkpoint s b := ra.step .round base code error apc
    have eb := round_exit a base apc
    have bbase : r (.GPR 8) b = address :=
      (guard_base .round a (by decide)).trans ea.1
    have bused : r (.GPR 9) b = used :=
      (guard_used .round a (by decide) (by decide)).trans ea.2.1
    have bwork : r (.GPR 10) b = r (.GPR 10) a := round_work a
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 40#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR 10) b)
        (by rw [bwork, addressNat]; exact roundOK)).2
      rw [bwork, addressNat] at padding
      let c := block Guard.align.ops b
      have rc : Checkpoint s c := rb.step .align base code error bpc
      have ec := align_exit b base bpc
      have cbase : r (.GPR 8) c = address :=
        (guard_base .align b (by decide)).trans bbase
      have padding' : (((r (.GPR 10) b + 7#64) &&& ~~~7#64) -
          r (.GPR 10) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [bwork] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 60#64 := by
          have exit := ec.2.2
          rw [padding', bused] at exit
          exact exit.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 9) c).toNat =
            SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.1, BitVec.toNat_add, padding', bused]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block Guard.finish.ops c
        have rd : Checkpoint s d := rc.step .finish base code error cpc
        have ed := finish_exit c base cpc
        have dbase : r (.GPR 8) d = address :=
          (guard_base .finish c (by decide)).trans cbase
        have dused : (r (.GPR 9) d).toNat =
            SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat (guard_used .finish c (by decide) (by decide))).trans startNat
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat 5 < 2^64
        · have dpc : read_pc d = base + 68#64 := by
            rw [startNat] at ed
            exact ed.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block Guard.capacity.ops d
          have re : Checkpoint s e := rd.step .capacity base code error dpc
          have ee := capacity_exit d base dpc
          have capLoad : read_mem_bytes 8 (r (.GPR 1) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR 9) d + 40#64).toNat =
              SszNative.Arena.finish address.toNat used.toNat 5 := by
            rw [BitVec.toNat_add, dused]
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat 5 ≤ capacity.toNat
          · have epc : read_pc e = base + 84#64 := by
              have exit := ee.2.2
              rw [capLoad, finishNat] at exit
              exact exit.trans (if_neg (by omega))
            obtain ⟨fuel, runs⟩ := re.runs
            refine ⟨fuel, e, runs, re, Or.inr ⟨?_, epc, ?_, ?_, ?_⟩⟩
            · exact ⟨by decide, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (guard_base .capacity d (by decide)).trans dbase
            · exact (congrArg BitVec.toNat
                (guard_used .capacity d (by decide) (by decide))).trans dused
            · rw [ee.2.1]
              exact finishNat
          · apply checks_failure s e base address capacity used re
            · have exit := ee.2.2
              rw [capLoad, finishNat] at exit
              exact exit.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply checks_failure s d base address capacity used rd
          · rw [startNat] at ed
            exact ed.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply checks_failure s c base address capacity used rc
        · have exit := ec.2.2
          rw [padding', bused] at exit
          exact exit.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply checks_failure s b base address capacity used rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply checks_failure s a base address capacity used ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1

/-- The one-Plan specialization agrees with the shared ordered reservation
transition, including failure-side cursor retention and its effect event. -/
theorem reservePlans_one (arena : SszNative.Delimited.ArenaState) :
    SszNative.CodecMeasure.reservePlans 1 arena =
      match SszNative.Arena.reserve arena.base arena.capacity arena.used 5 with
      | none => ⟨.error (.primitive (.arithmetic .scratchExhausted)), arena.used,
          [.reservePlans 1 arena none]⟩
      | some allocation => ⟨.ok allocation, allocation.used,
          [.reservePlans 1 arena (some allocation)]⟩ := by
  rfl

end SszArm.Codec.Measure.Singleton
