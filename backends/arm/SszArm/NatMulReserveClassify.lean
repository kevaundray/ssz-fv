import SszArm.NatMulReserveChecks

namespace SszArm.NatMul

/-- Complete classification of a read-only reservation-guard prefix. -/
def ReserveChecksPost (s t : ArmState) (base address capacity used : BitVec 64)
    (words successPC : Nat) (pointerReg startReg finishReg : BitVec 5) : Prop :=
  ReserveCheckpoint s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = none ∧
        read_pc t = base + 1076#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words ∧
        read_pc t = base + BitVec.ofNat 64 successPC ∧
        r (.GPR pointerReg) t = address ∧
        (r (.GPR startReg) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR finishReg) t).toNat = SszNative.Arena.finish address.toNat used.toNat words))

private theorem reserve_checks_failure (s t : ArmState)
    (base address capacity used : BitVec 64) (words successPC : Nat)
    (pointerReg startReg finishReg : BitVec 5) (positive : 0 < words)
    (reached : ReserveCheckpoint s t) (hp : read_pc t = base + 1076#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words) :
    ∃ fuel t, run fuel s = t ∧
      ReserveChecksPost s t base address capacity used words successPC pointerReg startReg finishReg := by
  obtain ⟨fuel, hr⟩ := reached.runs
  refine ⟨fuel, t, hr, ⟨reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ words positive).2 failed, hp⟩⟩⟩

/-- Real big-reservation checks, including all five failure exits. -/
theorem reserve_checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (words : Nat) (positive : 0 < words) (layout : 8 * words < 2^63)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 472#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (bytes : (r (.GPR 2#5) s).toNat = 8 * words)
    : ∃ fuel t, run fuel s = t ∧
      ReserveChecksPost s t base address capacity used words 536 10#5 11#5 12#5 := by
  let a := block base ReserveCheckKind.address.ops s
  have ra : ReserveCheckpoint s a := (ReserveCheckpoint.refl s).step .address base hc he ha hp
  have ea := reserve_address_exit s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 488#64 := by
      exact ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 12#5) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base ReserveCheckKind.round.ops a
    have rb : ReserveCheckpoint s b := ra.step .round base hc he ha apc
    have eb := reserve_round_exit a base
    have b8 : r (.GPR 10#5) b = address :=
      (reserve_guard_registers .round a base 10#5 (by decide)).trans ea.1
    have b9 : r (.GPR 11#5) b = used :=
      (reserve_guard_registers .round a base 11#5 (by decide)).trans ea.2.1
    have b10 : r (.GPR 12#5) b = r (.GPR 12#5) a :=
      reserve_guard_registers .round a base 12#5 (by decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 496#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR 12#5) b)
        (by rw [b10, addressNat]; exact roundOK)).2
      rw [b10, addressNat] at padding
      let c := block base ReserveCheckKind.align.ops b
      have rc : ReserveCheckpoint s c := rb.step .align base hc he ha bpc
      have ec := reserve_align_exit b base
      have c8 : r (.GPR 10#5) c = address :=
        (reserve_guard_registers .align b base 10#5 (by decide)).trans b8
      have padding' : (((r (.GPR 12#5) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR 12#5) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [b10] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 516#64 := by
          have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 11#5) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.2.1, BitVec.toNat_add, padding', b9]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block base ReserveCheckKind.finish.ops c
        have rd : ReserveCheckpoint s d := rc.step .finish base hc he ha cpc
        have ed := reserve_end_exit c base
        have d8 : r (.GPR 10#5) d = address :=
          (reserve_guard_registers .finish c base 10#5 (by decide)).trans c8
        have d9 : (r (.GPR 11#5) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (reserve_guard_registers .finish c base 11#5 (by decide))).trans startNat
        have c11 : (r (.GPR 2#5) c).toNat = 8 * words := by
          rw [reserve_guard_registers .align b base 2#5 (by decide),
            reserve_guard_registers .round a base 2#5 (by decide),
            reserve_guard_registers .address s base 2#5 (by decide)]
          exact bytes
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat words < 2^64
        · have dpc : read_pc d = base + 524#64 := by
            have edpc := ed.2
            rw [startNat, c11] at edpc
            exact edpc.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block base ReserveCheckKind.capacity.ops d
          have re : ReserveCheckpoint s e := rd.step .capacity base hc he ha dpc
          have ee := reserve_capacity_exit d base
          have capLoad : read_mem_bytes 8 (r (.GPR 5#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR 12#5) d).toNat =
              SszNative.Arena.finish address.toNat used.toNat words := by
            rw [ed.1, BitVec.toNat_add, startNat, c11]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat words ≤ capacity.toNat
          · have epc : read_pc e = base + 536#64 := by
              have hepc := ee.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_neg (by omega))
            obtain ⟨fuel, hrun⟩ := re.runs
            refine ⟨fuel, e, hrun, re, Or.inr ⟨?_, epc, ?_, ?_, ?_⟩⟩
            · exact ⟨layout, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (reserve_guard_registers .capacity d base 10#5 (by decide)).trans d8
            · exact (congrArg BitVec.toNat
                (reserve_guard_registers .capacity d base 11#5 (by decide))).trans d9
            · exact (congrArg BitVec.toNat
                (reserve_guard_registers .capacity d base 12#5 (by decide))).trans finishNat
          · apply reserve_checks_failure s e base address capacity used words 536 10#5 11#5 12#5 positive re
            · have hepc := ee.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply reserve_checks_failure s d base address capacity used words 536 10#5 11#5 12#5 positive rd
          · have edpc := ed.2
            rw [startNat, c11] at edpc
            exact edpc.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply reserve_checks_failure s c base address capacity used words 536 10#5 11#5 12#5 positive rc
        · have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply reserve_checks_failure s b base address capacity used words 536 10#5 11#5 12#5 positive rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply reserve_checks_failure s a base address capacity used words 536 10#5 11#5 12#5 positive ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1


end SszArm.NatMul
