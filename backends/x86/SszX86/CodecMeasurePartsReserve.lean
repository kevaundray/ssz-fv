import SszX86.CodecMeasurePartsReserveExec
import SszX86.CodecMeasureChildStorage

namespace SszX86.CodecMeasureParts
open UintCodec

/-- Only allocator work registers can change before the native cursor commit. -/
def GuardFrame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 →
    t.regs.get64 r = s.regs.get64 r

def ready (s : MachineData) (address used : BitVec 64) (count : Nat)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec address,
    rdx := UInt64.ofBitVec (used + address),
    r13 := UInt64.ofBitVec (((used + address) + 7) &&& ~~~7#64),
    rax := UInt64.ofNat (SszNative.Arena.start address.toNat used.toNat),
    rcx := UInt64.ofNat (SszNative.Arena.start address.toNat used.toNat + 40 * count)},
    status := flags}

def Reserved (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (count : Nat) (t : MachineState) : Prop :=
  GuardFrame s t.1 ∧
  ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (5 * count) = none ∧
      t.2 = base + 1021) ∨
    ∃ reservation,
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (5 * count) =
        some reservation ∧
      reservation.pointer = address.toNat + SszNative.Arena.start address.toNat used.toNat ∧
      reservation.used = SszNative.Arena.start address.toNat used.toNat + 40 * count ∧
      t.2 = base + 414 ∧ ∃ flags, t.1 = ready s address used count flags)

macro "codec_parts_guard_frame" : tactic => `(tactic|
  (refine ⟨rfl, rfl, ?_⟩
   intro r h1 h2 h3 h4 h5
   cases r <;> simp_all [flagged, addressed, aligned, ended, ready, Reg64s.get64]))

private theorem word_eq (word : BitVec 64) (n : Nat) (equal : word.toNat = n) :
    word = BitVec.ofNat 64 n := by
  rw [← equal, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The unchecked native multiplication is justified by the original Value
slice's physical isize bound. This is not a cap on logical Nat metadata. -/
theorem paired_plan_bytes_bound {m : DataMem} {r : SszX86.Codec.Footprint}
    {p : BitVec 64} {capture : CodecMeasureChild.Capture}
    {parts : SszNative.CodecMeasure.Parts} {values : List SszNative.Codec.Value}
    {keep : Bool} (stored : CodecMeasureChild.CaptureAt m r p capture parts values keep) :
    40 * parts.paired values < 2 ^ 63 := by
  have bytes := stored.valuesSlice.byteBound
  have paired : parts.paired values ≤ values.length := by
    cases parts with
    | repeated _ => exact Nat.le_refl _
    | fields fields => exact Nat.min_le_right _ _
  omega

/-- The actual variable-size inlined reservation implements all checked failure
branches before the cursor commit. Its logical model is precisely reservePlans'
five-u64 representation of native 40-byte Plan arrays. -/
theorem reserve_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64) (count : Nat)
    (header : Header s address capacity used)
    (registerCount : s.regs.rbx = UInt64.ofNat count)
    (positive : 0 < count) (bytesBound : 40 * count < 2 ^ 63) :
    Eventually (step e) (Reserved s base address capacity used count) (s, base + 331) := by
  have positiveWords : 0 < 5 * count := by omega
  have productWord : s.regs.rbx.toBitVec * 40 = BitVec.ofNat 64 (40 * count) := by
    rw [registerCount, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    exact BitVec.mul_comm _ _
  have product : (s.regs.rbx.toBitVec * 40).toNat = 40 * count := by
    rw [productWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have failure (notChecks : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat (5 * count)) :
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (5 * count) = none :=
    (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ positiveWords).2 notChecks
  apply address_cps e base code s address used header.address_load header.used_load
  intro f0
  by_cases addressOk : address.toNat + used.toNat < 2 ^ 64
  · have addressOk' : used.toNat + address.toNat < 2 ^ 64 := by omega
    rw [ite_eq_left addressOk']
    have sum : (used + address).toNat = address.toNat + used.toNat := by
      rw [UintCodec.Arena.add_nat used address addressOk']
      omega
    apply rounding_cps e base code
    intro f1
    simp only [addressed, sum, UInt64.toNat_ofBitVec]
    by_cases roundedOk : address.toNat + used.toNat + 7 < 2 ^ 64
    · rw [ite_eq_left roundedOk]
      have pad : (paddingWord (used + address)).toNat =
          SszNative.Arena.padding (address.toNat + used.toNat) := by
        rw [UintCodec.Arena.padding_nat _ (by rw [sum]; exact roundedOk), sum]
      apply alignment_cps e base code
      intro f2
      simp only [flagged, addressed, pad, UInt64.toNat_ofBitVec]
      by_cases startOk : SszNative.Arena.start address.toNat used.toNat < 2 ^ 64
      · have startOk' : SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2 ^ 64 := by
          simpa [SszNative.Arena.start, Nat.add_comm] using startOk
        rw [ite_eq_left startOk']
        have startNat : (paddingWord (used + address) + used).toNat =
            SszNative.Arena.start address.toNat used.toNat := by
          rw [UintCodec.Arena.add_nat _ _ (by rw [pad]; exact startOk'), pad]
          simp [SszNative.Arena.start, Nat.add_comm]
        have startWord := word_eq _ _ startNat
        apply ending_cps e base code
        intro f3
        simp only [flagged, aligned, addressed, startNat, UInt64.toNat_ofBitVec, product]
        by_cases endOk : SszNative.Arena.start address.toNat used.toNat + 40 * count < 2 ^ 64
        · rw [ite_eq_left (show 40 * count + SszNative.Arena.start address.toNat used.toNat < 2 ^ 64 by omega)]
          have endNat : (s.regs.rbx.toBitVec * 40 + (paddingWord (used + address) + used)).toNat =
              SszNative.Arena.start address.toNat used.toNat + 40 * count := by
            rw [UintCodec.Arena.add_nat _ _ (by rw [product, startNat]; omega), product, startNat]
            omega
          have endWord := word_eq _ _ endNat
          apply capacity_cps e base code (capacity := capacity)
          · exact header.capacity_load
          intro f4
          simp only [flagged, ended, aligned, addressed, endNat]
          by_cases fits : SszNative.Arena.start address.toNat used.toNat + 40 * count ≤ capacity.toNat
          · rw [ite_eq_left fits]
            have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat (5 * count) := by
              refine ⟨by omega, addressOk, roundedOk, startOk, ?_, ?_⟩
              · simpa only [SszNative.Arena.finish, ← Nat.mul_assoc] using endOk
              · simpa only [SszNative.Arena.finish, ← Nat.mul_assoc] using fits
            have success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (5 * count) =
                some ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                  SszNative.Arena.start address.toNat used.toNat + 40 * count⟩ := by
              apply (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ positiveWords _).2
              exact ⟨checks, by simp only [SszNative.Arena.finish, ← Nat.mul_assoc]⟩
            apply Eventually.done
            refine ⟨?_, Or.inr ⟨_, success, rfl, rfl, rfl, f4, ?_⟩⟩
            · codec_parts_guard_frame
            · simp only [flagged, ended, aligned, addressed, ready, startWord, endWord]
          · rw [ite_eq_right fits]
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (by
              intro checks
              apply fits
              simpa only [SszNative.Arena.finish, ← Nat.mul_assoc] using checks.2.2.2.2.2), rfl⟩⟩
            codec_parts_guard_frame
        · rw [ite_eq_right (show ¬ 40 * count + SszNative.Arena.start address.toNat used.toNat < 2 ^ 64 by omega)]
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (by
            intro checks
            apply endOk
            simpa only [SszNative.Arena.finish, ← Nat.mul_assoc] using checks.2.2.2.2.1), rfl⟩⟩
          codec_parts_guard_frame
      · have noStart : ¬ SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2 ^ 64 := by
          simpa [SszNative.Arena.start, Nat.add_comm] using startOk
        rw [ite_eq_right noStart]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (by intro checks; exact startOk checks.2.2.2.1), rfl⟩⟩
        codec_parts_guard_frame
    · rw [ite_eq_right roundedOk]
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (by intro checks; exact roundedOk checks.2.2.1), rfl⟩⟩
      codec_parts_guard_frame
  · have noAddress : ¬ used.toNat + address.toNat < 2 ^ 64 := by omega
    rw [ite_eq_right noAddress]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (by intro checks; exact addressOk checks.2.1), rfl⟩⟩
    codec_parts_guard_frame

end SszX86.CodecMeasureParts
