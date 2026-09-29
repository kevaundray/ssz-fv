import SszArm.CodecMeasurePartsReserveGuards
import SszCodecMeasure

set_option autoImplicit false

namespace SszArm.Codec.Measure.PartsReserve

private theorem guard_rounded (guard : Guard) (s : ArmState) (notAlign : guard ≠ .align) :
    r (.GPR 9) (block guard.ops s) = r (.GPR 9) s := by
  cases guard <;> simp_all [block, Guard.ops, effect, Udivti3.next, Udivti3.put,
    Udivti3.flagged, Udivti3.compare, Udivti3.branch, state_simp_rules]

def ChecksPost (s t : ArmState) (base address capacity used count : BitVec 64) : Prop :=
  Checkpoint s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (5 * count.toNat) = none ∧
        read_pc t = base + 960#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat (5 * count.toNat) ∧
        read_pc t = base + 436#64 ∧ r (.GPR 8) t = address ∧
        (r (.GPR 10) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR 11) t).toNat = SszNative.Arena.finish address.toNat used.toNat (5 * count.toNat) ∧
        (r (.GPR 9) t).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat))

private theorem checks_failure (s t : ArmState) (base address capacity used count : BitVec 64)
    (positive : 0 < count.toNat) (reached : Checkpoint s t) (pc : read_pc t = base + 960#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat (5 * count.toNat)) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used count := by
  obtain ⟨fuel, runs⟩ := reached.runs
  exact ⟨fuel, t, runs, reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by omega)).2 failed, pc⟩⟩

/-- Positive retained Plan reservations follow the actual unchecked-multiply
lowering, whose arithmetic is justified by physical Value-slice geometry.
No arena cursor validity or successful reservation is assumed. -/
theorem checks_runs (s : ArmState) (base address capacity used count : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 364#64)
    (positive : 0 < count.toNat) (physical : 40 * count.toNat < 2^63)
    (countRegister : r (.GPR 26) s = count)
    (headerBase : read_mem_bytes 8 (r (.GPR 20) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 20) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 20) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used count := by
  let a := block Guard.address.ops s
  have ra : Checkpoint s a := (Checkpoint.refl s).step .address base code error pc
  have ea := address_exit s base pc
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 380#64 := ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 11) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block Guard.round.ops a
    have rb : Checkpoint s b := ra.step .round base code error apc
    have eb := round_exit a base apc
    have bbase : r (.GPR 8) b = address := (guard_base .round a (by decide)).trans ea.1
    have bused : r (.GPR 10) b = used :=
      (guard_used .round a (by decide) (by decide)).trans ea.2.1
    have bwork : r (.GPR 11) b = r (.GPR 11) a := round_work a
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 388#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have geometry := Delimited.reservation_padding (r (.GPR 11) b)
        (by rw [bwork, addressNat]; exact roundOK)
      let c := block Guard.align.ops b
      have rc : Checkpoint s c := rb.step .align base code error bpc
      have ec := align_exit b base bpc
      have cbase : r (.GPR 8) c = address := (guard_base .align b (by decide)).trans bbase
      have padding : (((r (.GPR 11) b + 7#64) &&& ~~~7#64) - r (.GPR 11) b).toNat =
          SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [bwork, addressNat] using geometry.2
      have rounded : (r (.GPR 9) c).toNat =
          address.toNat + SszNative.Arena.start address.toNat used.toNat := by
        rw [ec.1, SszNative.Arena.start_pointer]
        simpa only [bwork, addressNat] using geometry.1
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 408#64 := by
          have exit := ec.2.2
          rw [padding, bused] at exit
          exact exit.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 10) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.1, BitVec.toNat_add, padding, bused]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have countC : r (.GPR 26) c = count :=
          (rc.fields (.GPR 26) (by decide)).trans countRegister
        have bytes := forty_count count physical
        let d := block Guard.finish.ops c
        have rd : Checkpoint s d := rc.step .finish base code error cpc
        have ed := finish_exit c base cpc
        have dbase : r (.GPR 8) d = address := (guard_base .finish c (by decide)).trans cbase
        have dused : (r (.GPR 10) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat (guard_used .finish c (by decide) (by decide))).trans startNat
        have drounded : (r (.GPR 9) d).toNat =
            address.toNat + SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat (guard_rounded .finish c (by decide))).trans rounded
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat (5 * count.toNat) < 2^64
        · have dpc : read_pc d = base + 424#64 := by
            have exit := ed.2
            rw [startNat, countC, bytes] at exit
            exact exit.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          have finishNat : (r (.GPR 11) d).toNat =
              SszNative.Arena.finish address.toNat used.toNat (5 * count.toNat) := by
            rw [ed.1, BitVec.toNat_add, startNat, countC, bytes]
            unfold SszNative.Arena.finish at *
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
          let e := block Guard.capacity.ops d
          have re : Checkpoint s e := rd.step .capacity base code error dpc
          have ee := capacity_exit d base dpc
          have capLoad : read_mem_bytes 8 (r (.GPR 20) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat (5 * count.toNat) ≤ capacity.toNat
          · have epc : read_pc e = base + 436#64 := by
              have exit := ee.2
              rw [capLoad, finishNat] at exit
              exact exit.trans (if_neg (by omega))
            obtain ⟨fuel, runs⟩ := re.runs
            refine ⟨fuel, e, runs, re, Or.inr ⟨?_, epc, ?_, ?_, ?_, ?_⟩⟩
            · exact ⟨by omega, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (guard_base .capacity d (by decide)).trans dbase
            · exact (congrArg BitVec.toNat
                (guard_used .capacity d (by decide) (by decide))).trans dused
            · exact (congrArg BitVec.toNat (capacity_work d)).trans finishNat
            · exact (congrArg BitVec.toNat (guard_rounded .capacity d (by decide))).trans drounded
          · apply checks_failure s e base address capacity used count positive re
            · have exit := ee.2
              rw [capLoad, finishNat] at exit
              exact exit.trans (if_pos (by omega))
            · exact fun checks => fits checks.2.2.2.2.2
        · apply checks_failure s d base address capacity used count positive rd
          · have exit := ed.2
            rw [startNat, countC, bytes] at exit
            exact exit.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · exact fun checks => finishOK checks.2.2.2.2.1
      · apply checks_failure s c base address capacity used count positive rc
        · have exit := ec.2.2
          rw [padding, bused] at exit
          exact exit.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · exact fun checks => startOK checks.2.2.2.1
    · apply checks_failure s b base address capacity used count positive rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · exact fun checks => roundOK checks.2.2.1
  · apply checks_failure s a base address capacity used count positive ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · exact fun checks => addressOK checks.2.1

/-- Rust's physical Value-slice bound suffices for every paired Plan count. -/
theorem paired_bytes_fit (parts : SszNative.CodecMeasure.Parts)
    (values : List SszNative.Codec.Value) (physical : 48 * values.length < 2^63) :
    40 * parts.paired values < 2^63 := by
  have paired : parts.paired values ≤ values.length := by
    cases parts <;> simp [SszNative.CodecMeasure.Parts.paired]
  omega

end SszArm.Codec.Measure.PartsReserve
