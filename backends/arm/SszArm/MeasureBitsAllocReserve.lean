import SszArm.MeasureBitsAllocMath

namespace SszArm.Measure.Bits.Alloc

def ChecksPost (site : Site) (s t : ArmState)
    (base address capacity used : BitVec 64) : Prop :=
  Checkpoint site s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none ∧
        read_pc t = base + 3528#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2 ∧
        read_pc t = base + BitVec.ofNat 64 (site.entry + 68) ∧
        r (.GPR site.baseReg) t = address ∧
        (r (.GPR site.usedReg) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR site.workReg) t).toNat = SszNative.Arena.finish address.toNat used.toNat 2))

private theorem checks_failure (site : Site) (s t : ArmState)
    (base address capacity used : BitVec 64)
    (reached : Checkpoint site s t) (pc : read_pc t = base + 3528#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost site s t base address capacity used := by
  obtain ⟨fuel, runs⟩ := reached.runs
  exact ⟨fuel, t, runs, reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ 2 (by decide)).2 failed, pc⟩⟩

/-- All three inlined allocators execute their own bytes. Invalid initial
cursors and every overflow are classified by the original five guards. -/
theorem checks_runs (site : Site) (s : ArmState) (base address capacity used : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 site.entry)
    (headerBase : read_mem_bytes 8 (r (.GPR 20#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 20#5) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost site s t base address capacity used := by
  let a := block site base CheckKind.address.ops s
  have ra : Checkpoint site s a := (Checkpoint.refl site s).step .address base code error aligned pc
  have ea := address_exit site s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + BitVec.ofNat 64 (site.entry + 16) :=
      ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR site.workReg) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block site base CheckKind.round.ops a
    have rb : Checkpoint site s b := ra.step .round base code error aligned apc
    have eb := round_exit site a base
    have bbase : r (.GPR site.baseReg) b = address :=
      (guard_registers site .round a base _ (by cases site <;> decide)).trans ea.1
    have bused : r (.GPR site.usedReg) b = used :=
      (guard_registers site .round a base _ (by cases site <;> decide)).trans ea.2.1
    have bwork : r (.GPR site.workReg) b = r (.GPR site.workReg) a :=
      guard_registers site .round a base _ (by cases site <;> decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + BitVec.ofNat 64 (site.entry + 24) := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR site.workReg) b)
        (by rw [bwork, addressNat]; exact roundOK)).2
      rw [bwork, addressNat] at padding
      let c := block site base CheckKind.align.ops b
      have rc : Checkpoint site s c := rb.step .align base code error aligned bpc
      have ec := align_exit site b base
      have cbase : r (.GPR site.baseReg) c = address :=
        (guard_registers site .align b base _ (by cases site <;> decide)).trans bbase
      have padding' : (((r (.GPR site.workReg) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR site.workReg) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [bwork] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + BitVec.ofNat 64 (site.entry + 44) := by
          have exit := ec.2.2
          rw [padding', bused] at exit
          exact exit.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR site.usedReg) c).toNat =
            SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.1, BitVec.toNat_add, padding', bused]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block site base CheckKind.finish.ops c
        have rd : Checkpoint site s d := rc.step .finish base code error aligned cpc
        have ed := finish_exit site c base
        have dbase : r (.GPR site.baseReg) d = address :=
          (guard_registers site .finish c base _ (by cases site <;> decide)).trans cbase
        have dused : (r (.GPR site.usedReg) d).toNat =
            SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (guard_registers site .finish c base _ (by cases site <;> decide))).trans startNat
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat 2 < 2^64
        · have dpc : read_pc d = base + BitVec.ofNat 64 (site.entry + 52) := by
            rw [startNat] at ed
            exact ed.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block site base CheckKind.capacity.ops d
          have re : Checkpoint site s e := rd.step .capacity base code error aligned dpc
          have ee := capacity_exit site d base
          have capLoad : read_mem_bytes 8 (r (.GPR 20#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR site.usedReg) d + 16#64).toNat =
              SszNative.Arena.finish address.toNat used.toNat 2 := by
            rw [BitVec.toNat_add, dused]
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat 2 ≤ capacity.toNat
          · have epc : read_pc e = base + BitVec.ofNat 64 (site.entry + 68) := by
              have exit := ee.2.2
              rw [capLoad, finishNat] at exit
              exact exit.trans (if_neg (by omega))
            obtain ⟨fuel, runs⟩ := re.runs
            refine ⟨fuel, e, runs, re, Or.inr ⟨?_, epc, ?_, ?_, ?_⟩⟩
            · exact ⟨by decide, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (guard_registers site .capacity d base _ (by cases site <;> decide)).trans dbase
            · exact (congrArg BitVec.toNat
                (guard_registers site .capacity d base _ (by cases site <;> decide))).trans dused
            · rw [ee.2.1]
              exact finishNat
          · apply checks_failure site s e base address capacity used re
            · have exit := ee.2.2
              rw [capLoad, finishNat] at exit
              exact exit.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply checks_failure site s d base address capacity used rd
          · rw [startNat] at ed
            exact ed.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply checks_failure site s c base address capacity used rc
        · have exit := ec.2.2
          rw [padding', bused] at exit
          exact exit.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply checks_failure site s b base address capacity used rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply checks_failure site s a base address capacity used ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1

end SszArm.Measure.Bits.Alloc
