import SszArm.NatMulWordReserveGuards

namespace SszArm.NatMulWord.Reserve

/-- The actual header guards do not write memory, on either exit. -/
def HeaderPost (width : Width) (words : Nat) (s t : ArmState)
    (base address capacity used : BitVec 64) : Prop :=
  Checkpoint s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = none ∧
        read_pc t = base + 1264#64) ∨
      (SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words ∧
        read_pc t = base + width.success ∧ r (.GPR 10#5) t = address ∧
        (r (.GPR width.startReg) t).toNat = SszNative.Arena.start address.toNat used.toNat ∧
        (r (.GPR width.finishReg) t).toNat = SszNative.Arena.finish address.toNat used.toNat words ∧
        (width = .large → r (.GPR 12#5) t = r (.GPR 12#5) s) ∧
        (width = .large → (r (.GPR 15#5) t).toNat =
          address.toNat + SszNative.Arena.start address.toNat used.toNat)))

private theorem header_failure (width : Width) (words : Nat) (positive : 0 < words)
    (s t : ArmState) (base address capacity used : BitVec 64)
    (reached : Checkpoint s t) (hp : read_pc t = base + 1264#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words) :
    ∃ fuel t, run fuel s = t ∧ HeaderPost width words s t base address capacity used := by
  obtain ⟨fuel, hr⟩ := reached.runs
  exact ⟨fuel, t, hr, reached, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ words positive).2 failed, hp⟩⟩

/-- Exact checked reservation, including malformed/overflowing current headers.
The byte-size guard has already run; no allocation or future-state premise occurs. -/
theorem header_checks_runs (width : Width) (words : Nat) (s : ArmState)
    (base address capacity used : BitVec 64) (positive : 0 < words)
    (size : 8 * words < 2^63) (bytes : (width.bytes s).toNat = 8 * words)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + Guard.address.entry width)
    (headerBase : read_mem_bytes 8 (r (.GPR 4#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ HeaderPost width words s t base address capacity used := by
  let a := block base (Guard.address.ops width) s
  have ra : Checkpoint s a := (Checkpoint.refl s).step width .address base hc he ha hp
  have ea := address_exit width s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + Guard.round.entry width :=
      ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR width.addressReg) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base (Guard.round.ops width) a
    have rb : Checkpoint s b := ra.step width .round base hc he ha apc
    have eb := round_exit width a base
    have bbase : r (.GPR 10#5) b = address :=
      (guard_registers width .round a base 10#5 (by cases width <;> decide)).trans ea.1
    have bused : r (.GPR width.usedReg) b = used :=
      (guard_registers width .round a base width.usedReg (by cases width <;> decide)).trans ea.2.1
    have baddress : r (.GPR width.addressReg) b = r (.GPR width.addressReg) a :=
      guard_registers width .round a base width.addressReg (by cases width <;> decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + Guard.align.entry width := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (Delimited.reservation_padding (r (.GPR width.addressReg) b)
        (by rw [baddress, addressNat]; exact roundOK)).2
      rw [baddress, addressNat] at padding
      let c := block base (Guard.align.ops width) b
      have rc : Checkpoint s c := rb.step width .align base hc he ha bpc
      have ec := align_exit width b base
      have cbase : r (.GPR 10#5) c = address :=
        (guard_registers width .align b base 10#5 (by cases width <;> decide)).trans bbase
      have padding' : (((r (.GPR width.addressReg) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR width.addressReg) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [baddress] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + Guard.finish.entry width := by
          have hcpc := ec.2.2
          rw [padding', bused] at hcpc
          exact hcpc.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR width.startReg) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.1, BitVec.toNat_add, padding', bused]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have cbytes : (width.bytes c).toNat = 8 * words := by
          dsimp only [c, b, a]
          rw [guard_bytes width .align _ base (by decide),
            guard_bytes width .round _ base (by decide),
            guard_bytes width .address _ base (by decide), bytes]
        let d := block base (Guard.finish.ops width) c
        have rd : Checkpoint s d := rc.step width .finish base hc he ha cpc
        have ed := finish_exit width c base
        have dbase : r (.GPR 10#5) d = address :=
          (guard_registers width .finish c base 10#5 (by cases width <;> decide)).trans cbase
        have dstart : (r (.GPR width.startReg) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (guard_registers width .finish c base width.startReg (by cases width <;> decide))).trans startNat
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat words < 2^64
        · have dpc : read_pc d = base + Guard.capacity.entry width := by
            have hdpc := ed.2
            rw [startNat, cbytes] at hdpc
            exact hdpc.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block base (Guard.capacity.ops width) d
          have re : Checkpoint s e := rd.step width .capacity base hc he ha dpc
          have ee := capacity_exit width d base
          have capLoad : read_mem_bytes 8 (r (.GPR 4#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (width.endValue d).toNat = SszNative.Arena.finish address.toNat used.toNat words := by
            rw [ed.1, BitVec.toNat_add, startNat, cbytes]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat words ≤ capacity.toNat
          · have epc : read_pc e = base + width.success := by
              have hepc := ee.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_neg (by omega))
            obtain ⟨fuel, hrun⟩ := re.runs
            refine ⟨fuel, e, hrun, re, Or.inr ⟨?_, epc, ?_, ?_, ?_, ?_, ?_⟩⟩
            · exact ⟨size, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact (guard_registers width .capacity d base 10#5 (by cases width <;> decide)).trans dbase
            · exact (congrArg BitVec.toNat
                (guard_registers width .capacity d base width.startReg (by cases width <;> decide))).trans dstart
            · rw [ee.1]
              exact finishNat
            · intro large
              subst width
              dsimp only [e, d, c, b, a]
              rw [guard_registers .large .capacity _ base 12#5 (by decide),
                guard_registers .large .finish _ base 12#5 (by decide),
                guard_registers .large .align _ base 12#5 (by decide),
                guard_registers .large .round _ base 12#5 (by decide),
                guard_registers .large .address _ base 12#5 (by decide)]
            · intro large
              subst width
              have ep : r (.GPR 15#5) e = r (.GPR 15#5) c :=
                (guard_registers .large .capacity d base 15#5 (by decide)).trans
                  (guard_registers .large .finish c base 15#5 (by decide))
              have alignedWord : r (.GPR 15#5) c =
                  (r (.GPR 14#5) b + 7#64) &&& 18446744073709551608#64 := by
                simpa only [Width.alignedReg, Width.addressReg] using ec.1
              have addressValue : (r (.GPR 14#5) b).toNat = address.toNat + used.toNat := by
                simpa only [Width.addressReg] using (congrArg BitVec.toNat baddress).trans addressNat
              rw [ep, alignedWord]
              have rounding := SszNative.Arena.mask_rounding (r (.GPR 14#5) b)
                (by rw [addressValue]; exact roundOK)
              rw [show (~~~(7 : BitVec 64)) = 18446744073709551608#64 by decide] at rounding
              rw [rounding, addressValue, SszNative.Arena.start_pointer]
          · apply header_failure width words positive s e base address capacity used re
            · have hepc := ee.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply header_failure width words positive s d base address capacity used rd
          · have hdpc := ed.2
            rw [startNat, cbytes] at hdpc
            exact hdpc.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply header_failure width words positive s c base address capacity used rc
        · have hcpc := ec.2.2
          rw [padding', bused] at hcpc
          exact hcpc.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply header_failure width words positive s b base address capacity used rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply header_failure width words positive s a base address capacity used ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1

theorem wide_checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 1132#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 4#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ HeaderPost .wide 2 s t base address capacity used :=
  header_checks_runs .wide 2 s base address capacity used (by decide) (by decide) rfl
    hc he ha hp headerBase headerCapacity headerUsed

/-- The successful machine registers denote the unique checked reservation. -/
theorem header_reservation (width : Width) (words : Nat) (positive : 0 < words)
    (s : ArmState) (address capacity used : BitVec 64)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words)
    (addressReg : r (.GPR 10#5) s = address)
    (startReg : (r (.GPR width.startReg) s).toNat = SszNative.Arena.start address.toNat used.toNat)
    (finishReg : (r (.GPR width.finishReg) s).toNat = SszNative.Arena.finish address.toNat used.toNat words) :
    SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words =
      some ⟨(r (.GPR 10#5) s).toNat + (r (.GPR width.startReg) s).toNat,
        (r (.GPR width.finishReg) s).toNat⟩ := by
  apply (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ positive _).2
  exact ⟨checks, by rw [addressReg, startReg, finishReg]⟩

/-- The pointer-forming ADD at PC1200/460 cannot wrap after these guards,
even without a signed capacity bound or a logical operand-length cap. -/
theorem header_pointer (width : Width) (words : Nat) (s : ArmState)
    (address capacity used : BitVec 64)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words)
    (addressReg : r (.GPR 10#5) s = address)
    (startReg : (r (.GPR width.startReg) s).toNat = SszNative.Arena.start address.toNat used.toNat) :
    (r (.GPR 10#5) s + r (.GPR width.startReg) s).toNat =
      address.toNat + SszNative.Arena.start address.toNat used.toNat := by
  have bound := (SszNative.Arena.aligned_bounds (address.toNat + used.toNat)).2
  have rounding := checks.2.2.1
  have pointer := SszNative.Arena.start_pointer address.toNat used.toNat
  rw [BitVec.toNat_add, addressReg, startReg]
  apply Nat.mod_eq_of_lt
  omega

end SszArm.NatMulWord.Reserve
