import SszArm.NatFromU128Guards

namespace SszArm.NatFromU128

/-- Guard exit classification; no successful reservation is assumed. -/
def ChecksPost (s t : ArmState) (base address capacity used : BitVec 64) : Prop :=
  Checkpoint s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none ∧
        read_pc t = base + 220#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2 ∧
        read_pc t = base + 156#64 ∧ r (.GPR 9#5) t = address ∧
        (r (.GPR 10#5) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR 11#5) t).toNat = SszNative.Arena.finish address.toNat used.toNat 2))

private theorem checks_failure (s t : ArmState)
    (base address capacity used : BitVec 64)
    (reached : Checkpoint s t) (hp : read_pc t = base + 220#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used := by
  obtain ⟨fuel, hr⟩ := reached.runs
  exact ⟨fuel, t, hr, reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ 2 (by decide)).2 failed, hp⟩⟩

/-- All five unsigned failure checks of the actual width-two reservation. -/
theorem checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 88#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 4#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used := by
  let a := block base CheckKind.address.ops s
  have ra : Checkpoint s a := (Checkpoint.refl s).step .address base hc he ha hp
  have ea := address_exit s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 104#64 :=
      ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 10#5) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base CheckKind.round.ops a
    have rb : Checkpoint s b := ra.step .round base hc he ha apc
    have eb := round_exit a base
    have b9 : r (.GPR 9#5) b = address :=
      (guard_registers .round a base 9#5 (by decide)).trans ea.1
    have b8 : r (.GPR 8#5) b = used :=
      (guard_registers .round a base 8#5 (by decide)).trans ea.2.1
    have b10 : r (.GPR 10#5) b = r (.GPR 10#5) a :=
      guard_registers .round a base 10#5 (by decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 112#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR 10#5) b)
        (by rw [b10, addressNat]; exact roundOK)).2
      rw [b10, addressNat] at padding
      let c := block base CheckKind.align.ops b
      have rc : Checkpoint s c := rb.step .align base hc he ha bpc
      have ec := align_exit b base
      have c9 : r (.GPR 9#5) c = address :=
        (guard_registers .align b base 9#5 (by decide)).trans b9
      have padding' : (((r (.GPR 10#5) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR 10#5) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [b10] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 132#64 := by
          have hcpc := ec.2.2
          rw [padding', b8] at hcpc
          exact hcpc.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 10#5) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.1, BitVec.toNat_add, padding', b8]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block base CheckKind.finish.ops c
        have rd : Checkpoint s d := rc.step .finish base hc he ha cpc
        have ed := finish_exit c base
        have d9 : r (.GPR 9#5) d = address :=
          (guard_registers .finish c base 9#5 (by decide)).trans c9
        have d10 : (r (.GPR 10#5) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (guard_registers .finish c base 10#5 (by decide))).trans startNat
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat 2 < 2^64
        · have dpc : read_pc d = base + 140#64 := by
            rw [startNat] at ed
            exact ed.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block base CheckKind.capacity.ops d
          have re : Checkpoint s e := rd.step .capacity base hc he ha dpc
          have ee := capacity_exit d base
          have capLoad : read_mem_bytes 8 (r (.GPR 4#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR 10#5) d + 16#64).toNat =
              SszNative.Arena.finish address.toNat used.toNat 2 := by
            rw [BitVec.toNat_add, d10]
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat 2 ≤ capacity.toNat
          · have epc : read_pc e = base + 156#64 := by
              have hepc := ee.2.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_neg (by omega))
            obtain ⟨fuel, hrun⟩ := re.runs
            refine ⟨fuel, e, hrun, re, Or.inr ⟨?_, epc, ?_, ?_, ?_⟩⟩
            · exact ⟨by decide, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (guard_registers .capacity d base 9#5 (by decide)).trans d9
            · exact (congrArg BitVec.toNat
                (guard_registers .capacity d base 10#5 (by decide))).trans d10
            · rw [ee.2.1]
              exact finishNat
          · apply checks_failure s e base address capacity used re
            · have hepc := ee.2.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply checks_failure s d base address capacity used rd
          · rw [startNat] at ed
            exact ed.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply checks_failure s c base address capacity used rc
        · have hcpc := ec.2.2
          rw [padding', b8] at hcpc
          exact hcpc.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
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

end SszArm.NatFromU128
