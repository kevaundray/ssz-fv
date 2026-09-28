import SszArm.NatMulWordWideFinish

namespace SszArm.NatMulWord

open SszNative.NatArithmetic
open Delimited (Protected)

/-- All five actual reservation guards are classified before any write. Original
Owned supplies only the selected physical write interval, not the entire arena. -/
theorem wide_run_from_current (s u : ArmState) (base factor : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned s operand factor)
    (priorFrame : SmallFrame s u) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc u = base + 1132#64)
    (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64) (small : operand.wordCount ≤ 1)
    (product : SszNative.NatMul.wordProduct operand factor = r (.GPR 9#5) u ++ r (.GPR 8#5) u)
    (wide : r (.GPR 9#5) u ≠ 0#64) :
    ∃ fuel t, run fuel u = t ∧ Post s t operand factor := by
  let address := read_mem_bytes 8 (r (.GPR 4#5) s) s
  let capacity := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
  let used := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s
  obtain ⟨fuel, v, vr, reached, selected⟩ := Reserve.wide_checks_runs u base address capacity used
    (priorFrame.code code) (priorFrame.error.trans error) (priorFrame.aligned aligned) pc
    (by simpa only [BitVec.ofNat_zero, BitVec.add_zero] using priorFrame.header owned 0 (by decide))
    (priorFrame.header owned 8 (by decide)) (priorFrame.header owned 16 (by decide))
  have frame : SmallFrame s v := priorFrame.trans reached.small
  rcases selected with ⟨failed, exit⟩ | ⟨checks, exit, baseReg, startReg, finishReg, _, _⟩
  · have model : outcome s operand factor = unchanged (arenaOf s).used (.error .scratchExhausted) :=
      Reserve.wide_failure_runWord operand factor (r (.GPR 8#5) u) (r (.GPR 9#5) u)
        address.toNat capacity.toNat used.toNat nonzero notone small product wide failed
    have finish := small_error_finish s v base factor operand owned frame code error aligned exit model
    exact ⟨fuel + 50, errorResult .scratch base v, by rw [run_plus, vr, finish.1], finish.2⟩
  · let reservation : SszNative.Arena.Reservation :=
      ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
        SszNative.Arena.finish address.toNat used.toNat 2⟩
    have model : outcome s operand factor =
        committed reservation [r (.GPR 8#5) u, r (.GPR 9#5) u] :=
      Reserve.wide_success_runWord operand factor (r (.GPR 8#5) u) (r (.GPR 9#5) u)
        address.toNat capacity.toNat used.toNat nonzero notone small product wide checks
    have pointer : (Reserve.widePointer v).toNat = reservation.pointer :=
      Reserve.header_pointer .wide 2 v address capacity used checks baseReg startReg
    have storage : address.toNat + capacity.toNat ≤ 2^64 := owned.arenaStorage
    have start := SszNative.Arena.used_le_start address.toNat used.toNat
    have fits := checks.2.2.2.2.2
    change SszNative.Arena.start address.toNat used.toNat + 16 ≤ capacity.toNat at fits
    have positive : 0 < address.toNat := owned.arenaNonnull (by change 0 < capacity.toNat; omega)
    have fresh := owned.fresh reservation (by simp [model, committed])
    have space : Reserve.WideSpace v := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [frame.arena] using owned.arenaBound
      · rw [pointer]
        change 0 < address.toNat + SszNative.Arena.start address.toNat used.toNat
        omega
      · rw [pointer]
        change (address.toNat + SszNative.Arena.start address.toNat used.toNat) % 8 = 0
        rw [SszNative.Arena.start_pointer]
        exact SszNative.Arena.aligned_mod _
      · rw [pointer]
        change address.toNat + SszNative.Arena.start address.toNat used.toNat + 16 ≤ 2^64
        omega
      · rcases fresh with empty | apart
        · simp [model, committed] at empty
        · have sep := apart ((r (.GPR 4#5) s).toNat, 24) (by simp)
          simp only [model, committed, List.length_cons, List.length_nil] at sep
          rw [frame.arena, pointer]
          omega
    obtain ⟨t, tr, post⟩ := wide_success_finish s v base factor
      (r (.GPR 8#5) u) (r (.GPR 9#5) u) operand reservation owned frame code error aligned exit space
      (reached.frame.registers _ (by decide)) (reached.frame.registers _ (by decide))
      wide pointer finishReg model
    exact ⟨fuel + 16, t, by rw [run_plus, vr, tr], post⟩

end SszArm.NatMulWord
