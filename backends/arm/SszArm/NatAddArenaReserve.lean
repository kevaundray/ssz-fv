import SszArm.NatAddArenaChecks

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete classification of a read-only reservation-guard prefix. -/
def ArenaChecksPost (s t : ArmState) (base address capacity used : BitVec 64)
    (words successPC : Nat) (pointerReg startReg finishReg : BitVec 5) : Prop :=
  ArenaCheckpoint s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = none ∧
        read_pc t = base + 1248#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words ∧
        read_pc t = base + BitVec.ofNat 64 successPC ∧
        r (.GPR pointerReg) t = address ∧
        (r (.GPR startReg) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR finishReg) t).toNat = SszNative.Arena.finish address.toNat used.toNat words))

private theorem arena_checks_failure (s t : ArmState)
    (base address capacity used : BitVec 64) (words successPC : Nat)
    (pointerReg startReg finishReg : BitVec 5) (positive : 0 < words)
    (extra : ArmState → Prop)
    (different : base + BitVec.ofNat 64 successPC ≠ base + 1248#64)
    (reached : ArenaCheckpoint s t) (hp : read_pc t = base + 1248#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words) :
    ∃ fuel t, run fuel s = t ∧
      ArenaChecksPost s t base address capacity used words successPC pointerReg startReg finishReg ∧
      (read_pc t = base + BitVec.ofNat 64 successPC → extra t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  refine ⟨fuel, t, hr, ⟨reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ words positive).2 failed, hp⟩⟩, ?_⟩
  intro success
  exact False.elim (different (success.symm.trans hp))

/-- Real small-reservation checks, including all five failure exits. -/
theorem arena_small_checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 1112#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    : ∃ fuel t, run fuel s = t ∧
      ArenaChecksPost s t base address capacity used 2 1180 8#5 10#5 11#5 ∧
      (read_pc t = base + 1180#64 → r (.GPR 9#5) t = r (.GPR 9#5) s) := by
  have positive : 0 < (2 : Nat) := by decide
  have layout : 8 * (2 : Nat) < 2^63 := by decide
  let a := block base ArenaCheckKind.smallAddress.ops s
  have ra : ArenaCheckpoint s a := (ArenaCheckpoint.refl s).step .smallAddress base hc he ha hp
  have ea := arena_small_address_exit s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 1128#64 := by
      exact ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 11#5) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base ArenaCheckKind.smallRound.ops a
    have rb : ArenaCheckpoint s b := ra.step .smallRound base hc he ha apc
    have eb := arena_small_round_exit a base
    have b8 : r (.GPR 8#5) b = address :=
      (arena_guard_registers .smallRound a base 8#5 (by decide)).trans ea.1
    have b9 : r (.GPR 10#5) b = used :=
      (arena_guard_registers .smallRound a base 10#5 (by decide)).trans ea.2.1
    have b10 : r (.GPR 11#5) b = r (.GPR 11#5) a :=
      arena_guard_registers .smallRound a base 11#5 (by decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 1136#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR 11#5) b)
        (by rw [b10, addressNat]; exact roundOK)).2
      rw [b10, addressNat] at padding
      let c := block base ArenaCheckKind.smallAlign.ops b
      have rc : ArenaCheckpoint s c := rb.step .smallAlign base hc he ha bpc
      have ec := arena_small_align_exit b base
      have c8 : r (.GPR 8#5) c = address :=
        (arena_guard_registers .smallAlign b base 8#5 (by decide)).trans b8
      have padding' : (((r (.GPR 11#5) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR 11#5) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [b10] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 1156#64 := by
          have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 10#5) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.2.1, BitVec.toNat_add, padding', b9]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block base ArenaCheckKind.smallEnd.ops c
        have rd : ArenaCheckpoint s d := rc.step .smallEnd base hc he ha cpc
        have ed := arena_small_end_exit c base
        have d8 : r (.GPR 8#5) d = address :=
          (arena_guard_registers .smallEnd c base 8#5 (by decide)).trans c8
        have d9 : (r (.GPR 10#5) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (arena_guard_registers .smallEnd c base 10#5 (by decide))).trans startNat
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat 2 < 2^64
        · have dpc : read_pc d = base + 1164#64 := by
            rw [startNat] at ed
            exact ed.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block base ArenaCheckKind.smallCapacity.ops d
          have re : ArenaCheckpoint s e := rd.step .smallCapacity base hc he ha dpc
          have ee := arena_small_capacity_exit d base
          have capLoad : read_mem_bytes 8 (r (.GPR 5#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR 10#5) d + 16#64).toNat =
              SszNative.Arena.finish address.toNat used.toNat 2 := by
            rw [BitVec.toNat_add, d9]
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat 2 ≤ capacity.toNat
          · have epc : read_pc e = base + 1180#64 := by
              have hepc := ee.2.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_neg (by omega))
            obtain ⟨fuel, hrun⟩ := re.runs
            refine ⟨fuel, e, hrun, ⟨re, Or.inr ⟨?_, epc, ?_, ?_, ?_⟩⟩, ?_⟩
            · exact ⟨layout, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (arena_guard_registers .smallCapacity d base 8#5 (by decide)).trans d8
            · exact (congrArg BitVec.toNat
                (arena_guard_registers .smallCapacity d base 10#5 (by decide))).trans d9
            · rw [ee.2.1]
              exact finishNat
            · intro _
              exact (arena_guard_registers .smallCapacity d base 9#5 (by decide)).trans
                ((arena_guard_registers .smallEnd c base 9#5 (by decide)).trans
                  ((arena_guard_registers .smallAlign b base 9#5 (by decide)).trans
                    ((arena_guard_registers .smallRound a base 9#5 (by decide)).trans
                      (arena_guard_registers .smallAddress s base 9#5 (by decide)))))
          · apply arena_checks_failure s e base address capacity used 2 1180 8#5 10#5 11#5 positive _ (by bv_omega) re
            · have hepc := ee.2.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply arena_checks_failure s d base address capacity used 2 1180 8#5 10#5 11#5 positive _ (by bv_omega) rd
          · rw [startNat] at ed
            exact ed.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply arena_checks_failure s c base address capacity used 2 1180 8#5 10#5 11#5 positive _ (by bv_omega) rc
        · have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply arena_checks_failure s b base address capacity used 2 1180 8#5 10#5 11#5 positive _ (by bv_omega) rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply arena_checks_failure s a base address capacity used 2 1180 8#5 10#5 11#5 positive _ (by bv_omega) ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1

/-- Real big-reservation checks, including all five failure exits. -/
theorem arena_big_checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (words : Nat) (positive : 0 < words) (layout : 8 * words < 2^63)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 204#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (bytes : (r (.GPR 11#5) s).toNat = 8 * words)
    : ∃ fuel t, run fuel s = t ∧
      ArenaChecksPost s t base address capacity used words 268 9#5 12#5 11#5 ∧
      (read_pc t = base + 268#64 →
        r (.GPR 8#5) t = r (.GPR 8#5) s ∧
        (r (.GPR 10#5) t).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat) := by
  let a := block base ArenaCheckKind.bigAddress.ops s
  have ra : ArenaCheckpoint s a := (ArenaCheckpoint.refl s).step .bigAddress base hc he ha hp
  have ea := arena_big_address_exit s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 220#64 := by
      exact ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 13#5) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base ArenaCheckKind.bigRound.ops a
    have rb : ArenaCheckpoint s b := ra.step .bigRound base hc he ha apc
    have eb := arena_big_round_exit a base
    have b8 : r (.GPR 9#5) b = address :=
      (arena_guard_registers .bigRound a base 9#5 (by decide)).trans ea.1
    have b9 : r (.GPR 12#5) b = used :=
      (arena_guard_registers .bigRound a base 12#5 (by decide)).trans ea.2.1
    have b10 : r (.GPR 13#5) b = r (.GPR 13#5) a :=
      arena_guard_registers .bigRound a base 13#5 (by decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 228#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR 13#5) b)
        (by rw [b10, addressNat]; exact roundOK)).2
      rw [b10, addressNat] at padding
      let c := block base ArenaCheckKind.bigAlign.ops b
      have rc : ArenaCheckpoint s c := rb.step .bigAlign base hc he ha bpc
      have ec := arena_big_align_exit b base
      have c8 : r (.GPR 9#5) c = address :=
        (arena_guard_registers .bigAlign b base 9#5 (by decide)).trans b8
      have padding' : (((r (.GPR 13#5) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR 13#5) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [b10] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 248#64 := by
          have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 12#5) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.2.1, BitVec.toNat_add, padding', b9]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block base ArenaCheckKind.bigEnd.ops c
        have rd : ArenaCheckpoint s d := rc.step .bigEnd base hc he ha cpc
        have ed := arena_big_end_exit c base
        have d8 : r (.GPR 9#5) d = address :=
          (arena_guard_registers .bigEnd c base 9#5 (by decide)).trans c8
        have d9 : (r (.GPR 12#5) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (arena_guard_registers .bigEnd c base 12#5 (by decide))).trans startNat
        have c11 : (r (.GPR 11#5) c).toNat = 8 * words := by
          rw [arena_guard_registers .bigAlign b base 11#5 (by decide),
            arena_guard_registers .bigRound a base 11#5 (by decide),
            arena_guard_registers .bigAddress s base 11#5 (by decide)]
          exact bytes
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat words < 2^64
        · have dpc : read_pc d = base + 256#64 := by
            have edpc := ed.2
            rw [startNat, c11] at edpc
            exact edpc.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block base ArenaCheckKind.bigCapacity.ops d
          have re : ArenaCheckpoint s e := rd.step .bigCapacity base hc he ha dpc
          have ee := arena_big_capacity_exit d base
          have capLoad : read_mem_bytes 8 (r (.GPR 5#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR 11#5) d).toNat =
              SszNative.Arena.finish address.toNat used.toNat words := by
            rw [ed.1, BitVec.toNat_add, startNat, c11]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat words ≤ capacity.toNat
          · have epc : read_pc e = base + 268#64 := by
              have hepc := ee.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_neg (by omega))
            obtain ⟨fuel, hrun⟩ := re.runs
            refine ⟨fuel, e, hrun, ⟨re, Or.inr ⟨?_, epc, ?_, ?_, ?_⟩⟩, ?_⟩
            · exact ⟨layout, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (arena_guard_registers .bigCapacity d base 9#5 (by decide)).trans d8
            · exact (congrArg BitVec.toNat
                (arena_guard_registers .bigCapacity d base 12#5 (by decide))).trans d9
            · exact (congrArg BitVec.toNat
                (arena_guard_registers .bigCapacity d base 11#5 (by decide))).trans finishNat
            · intro _
              constructor
              · exact (arena_guard_registers .bigCapacity d base 8#5 (by decide)).trans
                  ((arena_guard_registers .bigEnd c base 8#5 (by decide)).trans
                    ((arena_guard_registers .bigAlign b base 8#5 (by decide)).trans
                      ((arena_guard_registers .bigRound a base 8#5 (by decide)).trans
                        (arena_guard_registers .bigAddress s base 8#5 (by decide)))))
              · have aligned := (Delimited.reservation_padding (r (.GPR 13#5) b)
                  (by rw [b10, addressNat]; exact roundOK)).1
                rw [b10, addressNat] at aligned
                rw [arena_guard_registers .bigCapacity d base 10#5 (by decide),
                  arena_guard_registers .bigEnd c base 10#5 (by decide), ec.1]
                simpa only [b10] using
                  aligned.trans (SszNative.Arena.start_pointer address.toNat used.toNat).symm
          · apply arena_checks_failure s e base address capacity used words 268 9#5 12#5 11#5 positive _ (by bv_omega) re
            · have hepc := ee.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply arena_checks_failure s d base address capacity used words 268 9#5 12#5 11#5 positive _ (by bv_omega) rd
          · have edpc := ed.2
            rw [startNat, c11] at edpc
            exact edpc.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply arena_checks_failure s c base address capacity used words 268 9#5 12#5 11#5 positive _ (by bv_omega) rc
        · have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply arena_checks_failure s b base address capacity used words 268 9#5 12#5 11#5 positive _ (by bv_omega) rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply arena_checks_failure s a base address capacity used words 268 9#5 12#5 11#5 positive _ (by bv_omega) ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1

end SszArm.NatAdd
