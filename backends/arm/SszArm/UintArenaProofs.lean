import SszArm.UintArena

namespace SszArm.UintCodec

open BitVec
open SszArm.Udivti3 (adc_value adc_carry cmp_carry cmp_zero)

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- CMN #8 / B.HI is precisely the checked address+7 overflow guard. -/
theorem arena_round_guard (address : BitVec 64) :
    ((AddWithCarry address 8#64 0#1).2.c = 1#1 ∧
      (AddWithCarry address 8#64 0#1).2.z = 0#1) ↔
      2^64 ≤ address.toNat + 7 := by
  have hc := adc_carry address 8#64 0#1
  have hz : (AddWithCarry address 8#64 0#1).2.z = 0#1 ↔ address + 8#64 ≠ 0#64 := by
    change (if (AddWithCarry address 8#64 0#1).1 = 0#64 then 1#1 else 0#1) = 0#1 ↔ _
    rw [adc_value]
    simp
  rw [hz, hc]
  simp only [Udivti3.radix, BitVec.toNat_ofNat]
  bv_omega

theorem arena_capacity_guard (used capacity : BitVec 64) :
    ((AddWithCarry used (~~~capacity) 1#1).2.c = 1#1 ∧
      (AddWithCarry used (~~~capacity) 1#1).2.z = 0#1) ↔
      capacity.toNat < used.toNat := by
  have hz : (AddWithCarry used (~~~capacity) 1#1).2.z = 0#1 ↔ used ≠ capacity := by
    have h := cmp_zero used capacity
    have hb := (AddWithCarry used (~~~capacity) 1#1).2.z.isLt
    bv_omega
  rw [cmp_carry, hz]
  have he : used = capacity ↔ used.toNat = capacity.toNat :=
    ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  simp only [ne_eq, he]
  omega

def arenaBase (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 19) s) s
def arenaUsed (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 19) s + 16#64) s
def arenaCapacity (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 19) s + 8#64) s
def arenaAddress (s : ArmState) : BitVec 64 := arenaUsed s + arenaBase s
def arenaAligned (s : ArmState) : BitVec 64 := (arenaAddress s + 7#64) &&& ~~~7#64
def arenaPadding (s : ArmState) : BitVec 64 := arenaAligned s - arenaAddress s
def arenaStart (s : ArmState) : BitVec 64 := arenaPadding s + arenaUsed s
def arenaEnd (s : ArmState) : BitVec 64 := arenaStart s + r (.GPR 13) s

/-- Prefix lengths select the first failed native guard, or the committed path. -/
def arenaTrace (s : ArmState) : List Nat :=
  if 2^64 ≤ (arenaUsed s).toNat + (arenaBase s).toNat then List.range 4
  else if 2^64 ≤ (arenaAddress s).toNat + 7 then List.range 6
  else if 2^64 ≤ (arenaPadding s).toNat + (arenaUsed s).toNat then List.range 11
  else if 2^64 ≤ (arenaStart s).toNat + (r (.GPR 13) s).toNat then List.range 13
  else if (arenaCapacity s).toNat < (arenaEnd s).toNat then List.range 16
  else List.range 23

macro "arena_normalize" : tactic => `(tactic|
  simp_all (config := {decide := true, instances := true})
    [ArenaFollows, arenaBlock, arenaInstruction, List.range_succ,
     Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.flagged, Udivti3.branch,
     arenaEnd, arenaStart, arenaPadding, arenaAligned, arenaAddress,
     arenaBase, arenaUsed, arenaCapacity, adc_value,
     state_simp_rules, BitVec.add_assoc, ← Nat.not_lt, -BitVec.not_lt])

/-- Every selected prefix follows actual conditional branches, including all
overflow cases; the first failed guard exits before any arena write. -/
theorem arena_trace_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 6776#64) :
    ArenaFollows base (arenaTrace s) s := by
  have hA := adc_carry (arenaUsed s) (arenaBase s) 0#1
  have hR := arena_round_guard (arenaAddress s)
  have hS := adc_carry (arenaPadding s) (arenaUsed s) 0#1
  have hE := adc_carry (arenaStart s) (r (.GPR 13) s) 0#1
  have hC := arena_capacity_guard (arenaEnd s) (arenaCapacity s)
  simp only [Udivti3.radix, BitVec.toNat_ofNat] at hA hS hE
  change r .PC s = base + 6776#64 at hp
  unfold arenaTrace
  split
  · arena_normalize
  · split
    · arena_normalize
    · split
      · arena_normalize
      · split
        · arena_normalize
        · split <;> arena_normalize

theorem arena_runs (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 6776#64)
    (he : read_err s = .None) :
    run (arenaTrace s).length s = arenaBlock (arenaTrace s) s :=
  arena_block_run _ s base hc he (arena_trace_follows s base hp)

def ArenaPasses (s : ArmState) : Prop :=
  (arenaUsed s).toNat + (arenaBase s).toNat < 2^64 ∧
  (arenaAddress s).toNat + 7 < 2^64 ∧
  (arenaPadding s).toNat + (arenaUsed s).toNat < 2^64 ∧
  (arenaStart s).toNat + (r (.GPR 13) s).toNat < 2^64 ∧
  (arenaEnd s).toNat ≤ (arenaCapacity s).toNat

theorem arena_trace_full (s : ArmState) :
    (arenaTrace s).length = 23 ↔ ArenaPasses s := by
  unfold arenaTrace ArenaPasses
  split
  · simp_all <;> omega
  · split
    · simp_all <;> omega
    · split
      · simp_all <;> omega
      · split
        · simp_all <;> omega
        · split <;> simp_all <;> omega

theorem arena_address_nat (s : ArmState)
    (ha : (arenaBase s).toNat + (arenaUsed s).toNat < 2^64) :
    (arenaAddress s).toNat = (arenaBase s).toNat + (arenaUsed s).toNat := by
  rw [arenaAddress, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem arena_padding_nat (s : ArmState)
    (ha : (arenaBase s).toNat + (arenaUsed s).toNat < 2^64)
    (hr : (arenaBase s).toNat + (arenaUsed s).toNat + 7 < 2^64) :
    (arenaPadding s).toNat =
      SszNative.Arena.padding ((arenaBase s).toNat + (arenaUsed s).toNat) := by
  have haddr := arena_address_nat s ha
  have hround : (arenaAligned s).toNat =
      SszNative.Arena.aligned ((arenaBase s).toNat + (arenaUsed s).toNat) := by
    have h := SszNative.Arena.mask_rounding (arenaAddress s) (by simpa only [haddr] using hr)
    change ((arenaAddress s + 7#64) &&& ~~~7#64).toNat =
      SszNative.Arena.aligned (arenaAddress s).toNat at h
    simpa only [arenaAligned, haddr] using h
  have hle : arenaAddress s ≤ arenaAligned s := by
    change (arenaAddress s).toNat ≤ (arenaAligned s).toNat
    rw [haddr, hround]
    exact (SszNative.Arena.aligned_bounds _).1
  rw [arenaPadding, BitVec.toNat_sub_of_le hle, hround, haddr]
  rfl

/-- The word-valued machine guards equal the exact checked-arithmetic contract,
without assuming that the caller's arena itself is valid. -/
theorem arena_passes_iff_checks (s : ArmState) (words : Nat)
    (hb : (r (.GPR 13) s).toNat = 8 * words) (hi : 8 * words < 2^63) :
    ArenaPasses s ↔ SszNative.Arena.Checks
      (arenaBase s).toNat (arenaCapacity s).toNat (arenaUsed s).toNat words := by
  constructor
  · rintro ⟨ha, hr, hs, he, hc⟩
    have ha' : (arenaBase s).toNat + (arenaUsed s).toNat < 2^64 := by omega
    have haddr := arena_address_nat s ha'
    have hr' : (arenaBase s).toNat + (arenaUsed s).toNat + 7 < 2^64 := by
      simpa only [haddr] using hr
    have hpad := arena_padding_nat s ha' hr'
    have hstart : (arenaStart s).toNat =
        SszNative.Arena.start (arenaBase s).toNat (arenaUsed s).toNat := by
      rw [arenaStart, BitVec.toNat_add, Nat.mod_eq_of_lt hs, hpad]
      simp only [SszNative.Arena.start, Nat.add_comm]
    have hend : (arenaEnd s).toNat =
        SszNative.Arena.finish (arenaBase s).toNat (arenaUsed s).toNat words := by
      rw [arenaEnd, BitVec.toNat_add, Nat.mod_eq_of_lt he, hstart, hb]
      rfl
    refine ⟨hi, ha', hr', ?_, ?_, ?_⟩
    · rw [hpad] at hs
      simpa only [SszNative.Arena.start, Nat.add_comm] using hs
    · simpa only [hstart, hb, SszNative.Arena.finish] using he
    · simpa only [hend] using hc
  · rintro ⟨_, ha, hr, hs, he, hc⟩
    have haddr := arena_address_nat s ha
    have hpad := arena_padding_nat s ha hr
    have hs' : (arenaPadding s).toNat + (arenaUsed s).toNat < 2^64 := by
      simpa only [hpad, SszNative.Arena.start, Nat.add_comm] using hs
    have hstart : (arenaStart s).toNat =
        SszNative.Arena.start (arenaBase s).toNat (arenaUsed s).toNat := by
      rw [arenaStart, BitVec.toNat_add, Nat.mod_eq_of_lt hs', hpad]
      simp only [SszNative.Arena.start, Nat.add_comm]
    have he' : (arenaStart s).toNat + (r (.GPR 13) s).toNat < 2^64 := by
      simpa only [hstart, hb, SszNative.Arena.finish] using he
    have hend : (arenaEnd s).toNat =
        SszNative.Arena.finish (arenaBase s).toNat (arenaUsed s).toNat words := by
      rw [arenaEnd, BitVec.toNat_add, Nat.mod_eq_of_lt he', hstart, hb]
      rfl
    exact ⟨by omega, by simpa only [haddr] using hr, hs', he', by simpa only [hend] using hc⟩

theorem arenaBlock_field (ks : List Nat) (s : ArmState) (f : StateField)
    (hf : ArenaPreserved f) : r f (arenaBlock ks s) = r f s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rw [arenaBlock, ih, arenaInstruction_field k s f hf]

/-- The actual trace commits precisely one cursor word on success and nothing
on failure; it also establishes every register needed by the limb-fill loop. -/
theorem arena_trace_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 6776#64) :
    let t := arenaBlock (arenaTrace s) s
    read_pc t = (if (arenaTrace s).length = 23 then base + 6920#64 else base + 4816#64) ∧
    t.mem = (if (arenaTrace s).length = 23 then
      write_mem_bytes 8 (r (.GPR 19) s + 16#64) (arenaEnd s) s else s).mem ∧
    ((arenaTrace s).length = 23 →
      r (.GPR 12) t = arenaBase s + arenaStart s ∧
      r (.GPR 16) t = arenaEnd s ∧
      r (.GPR 8) t = r (.GPR 8) s + 1#64 ∧
      r (.GPR 13) t = 0#64 ∧ r (.GPR 14) t = 0#64 ∧ r (.GPR 15) t = 8#64) := by
  have hA := adc_carry (arenaUsed s) (arenaBase s) 0#1
  have hR := arena_round_guard (arenaAddress s)
  have hS := adc_carry (arenaPadding s) (arenaUsed s) 0#1
  have hE := adc_carry (arenaStart s) (r (.GPR 13) s) 0#1
  have hC := arena_capacity_guard (arenaEnd s) (arenaCapacity s)
  simp only [Udivti3.radix, BitVec.toNat_ofNat] at hA hS hE
  change r .PC s = base + 6776#64 at hp
  dsimp only
  unfold arenaTrace
  split
  · arena_normalize
  · split
    · arena_normalize
    · split
      · arena_normalize
      · split
        · arena_normalize
        · split
          · arena_normalize
          · arena_normalize
            apply mem_write_mem_bytes_of_mem_eq
            simp [state_simp_rules]

theorem arenaBlock_program (ks : List Nat) (s : ArmState) :
    (arenaBlock ks s).program = s.program := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => rw [arenaBlock, ih, arenaInstruction_program]

theorem arenaBlock_code (ks : List Nat) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) : CodeAt (arenaBlock ks s) base := by
  intro row hr
  simpa only [arenaBlock_program] using hc row hr

end SszArm.UintCodec
