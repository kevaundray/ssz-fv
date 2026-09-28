import SszX86.MeasureBytesState

namespace SszX86.Measure.Bytes
open Kraken.X64.Parser UintCodec SszNative.Limbs

theorem list_scalar (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P (state s a c si x y fl,
      if s.regs.rax.toNat ≤ si.toNat then base + 3050 else base + 2252)) :
    Eventually (step e) P (state s a c si x y fl, base + 2243) := by
  have target := hc.targets ("measure_u3050", 3050) (by decide)
  measure_bytes_step 327 using hc
  measure_bytes_step 328 using hc
  rcases Nat.lt_trichotomy s.regs.rax.toNat si.toNat with h | h | h
  · have hn : s.regs.rax.toBitVec ≠ si := by
      intro he
      have hh : s.regs.rax.toNat = si.toNat := congrArg BitVec.toNat he
      omega
    simpa [target, StatusFlags.from_result, h, hn, Nat.le_of_lt h, state, Effects.All]
      using hp _
  · have he : s.regs.rax.toBitVec = si := BitVec.eq_of_toNat_eq h
    simpa [target, StatusFlags.from_result, he, h, state, Effects.All] using hp _
  · have hn : s.regs.rax.toBitVec ≠ si := by
      intro he
      have hh : s.regs.rax.toNat = si.toNat := congrArg BitVec.toNat he
      omega
    simpa [StatusFlags.from_result, Nat.not_lt_of_ge (Nat.le_of_lt h), Nat.not_le_of_gt h,
      hn, state, Effects.All] using hp _

theorem list_small_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P (state s a c si x y fl,
      if s.regs.rax.toNat ≤ c.toNat then base + 3050 else base + 2252)) :
    Eventually (step e) P (state s a c si x y fl, base + 2217) := by
  have target := hc.targets ("measure_u3050", 3050) (by decide)
  measure_bytes_step 320 using hc
  constructor <;> measure_bytes_step 321 using hc
  all_goals measure_bytes_step 322 using hc
  all_goals measure_bytes_step 323 using hc
  all_goals measure_bytes_step 324 using hc
  all_goals measure_bytes_step 325 using hc
  all_goals constructor <;> measure_bytes_step 326 using hc
  all_goals
    by_cases hz : s.regs.rax.toBitVec = 0#64
    · have hzero : s.regs.rax.toNat = 0 := by simpa using congrArg BitVec.toNat hz
      simpa [target, StatusFlags.from_result, hz, hzero, state, Effects.All] using hp _ _ _ _
    · by_cases he : s.regs.rax.toBitVec = c
      · have heq : s.regs.rax.toNat = c.toNat := congrArg BitVec.toNat he
        simpa [target, StatusFlags.from_result, hz, he, heq, state, Effects.All] using hp _ _ _ _
      · simp [StatusFlags.from_result, hz, he, Effects.All]
        apply list_scalar e base hc
        intro fl'
        simpa [state] using hp c _ _ fl'

/-- Isolate the first nondeterministic TEST so later blocks are proved once. -/
theorem list_small_tag (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      (state s a c (if s.regs.rax.toBitVec = 0#64 then 0#64 else 1#64) x y fl,
        base + 1679)) :
    Eventually (step e) P (state s a c 0#64 x y fl, base + 1672) := by
  measure_bytes_step 222 using hc
  constructor <;> measure_bytes_step 223 using hc
  all_goals
    by_cases hz : s.regs.rax.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, state, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hz, state, Effects.All] using hp _

/-- A zero byte count takes the actual AND/JMP/TEST/JNE success tail. -/
theorem list_small_zero_tail (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P (state s a c 0#64 x y fl, base + 3050)) :
    Eventually (step e) P (state s a c 0#64 x y fl, base + 1699) := by
  measure_bytes_step 229 using hc
  constructor <;> measure_bytes_step 230 using hc
  all_goals measure_bytes_step 283 using hc
  all_goals constructor <;> measure_bytes_step 284 using hc
  all_goals simp [StatusFlags.from_result, Effects.All]
  all_goals measure_bytes_step 285 using hc
  all_goals simpa [state] using hp _

/-- A nonzero count and zero cap take the exact Limit tail. -/
theorem list_small_one_tail (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c y : BitVec 64) (high : BitVec 56) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      (state s a c 1#64 (high ++ 1#8) y fl, base + 2252)) :
    Eventually (step e) P (state s a c 1#64 (high ++ 1#8) y fl, base + 1699) := by
  have reject := hc.targets ("measure_u2252", 2252) (by decide)
  measure_bytes_step 229 using hc
  constructor <;> measure_bytes_step 230 using hc
  all_goals measure_bytes_step 283 using hc
  all_goals constructor <;> measure_bytes_step 284 using hc
  all_goals simpa [reject, StatusFlags.from_result, Effects.All, state] using hp _

theorem list_small (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P (state s a c si x y fl,
      if s.regs.rax.toNat ≤ c.toNat then base + 3050 else base + 2252)) :
    Eventually (step e) P (state s a c 0#64 x y fl, base + 1672) := by
  have target := hc.targets ("measure_u2217", 2217) (by decide)
  apply list_small_tag e base hc
  intro fl'
  all_goals measure_bytes_step 224 using hc
  all_goals constructor <;> measure_bytes_step 225 using hc
  all_goals measure_bytes_step 226 using hc
  all_goals measure_bytes_step 227 using hc
  all_goals constructor <;> measure_bytes_step 228 using hc
  all_goals
    by_cases hz : s.regs.rax.toBitVec = 0#64
    · by_cases hc0 : c = 0#64
      · simp [target, StatusFlags.from_result, hz, hc0, Effects.All]
        apply list_small_finish e base hc s a 0#64
        simpa only [hc0] using hp
      · simp [StatusFlags.from_result, hz, hc0, Effects.All]
        apply list_small_zero_tail e base hc
        intro fl''
        have hzero : s.regs.rax.toNat = 0 := by simpa using congrArg BitVec.toNat hz
        simpa [state, hzero] using hp 0#64 _ _ fl''
    · by_cases hc0 : c = 0#64
      · simp [StatusFlags.from_result, hz, hc0, Effects.All]
        apply list_small_one_tail e base hc
        intro fl''
        have hpos : 0 < s.regs.rax.toNat := by
          have hne : s.regs.rax.toNat ≠ 0 := by
            intro he
            exact hz (BitVec.eq_of_toNat_eq he)
          omega
        simpa [hc0, Nat.not_le_of_gt hpos, state] using hp 1#64 _ _ fl''
      · simp [target, StatusFlags.from_result, hz, hc0, Effects.All]
        exact list_small_finish e base hc s a c _ _ _ _ P hp

end SszX86.Measure.Bytes
