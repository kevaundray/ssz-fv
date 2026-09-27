import SszX86.DelimitedCore

namespace SszX86.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def scanState (s : MachineData) (i : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat i}, status := flags}

/-- The linked forward scan increments after the byte read and never reads at
length, including the physical maximum usize length. -/
theorem scan_iteration (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (i : Nat) (flags : StatusFlags)
    (length : data.size = s.regs.rcx.toNat) (within : i ≤ data.size)
    (bytes : UintCodec.Large.BytesAt s.dmem s.regs.rdx.toBitVec data)
    (P : MachineState → Prop)
    (done : i = data.size → ∀ flags,
      Eventually (step e) P (scanState s i flags, base + 582))
    (zero : i < data.size → data[i]?.getD 0 = 0 → ∀ flags,
      Eventually (step e) P (scanState s (i+1) flags, base + 240))
    (nonzero : i < data.size → data[i]?.getD 0 ≠ 0 → ∀ flags,
      Eventually (step e) P (scanState s (i+1) flags, base + 259)) :
    Eventually (step e) P (scanState s i flags, base + 240) := by
  have bound : data.size < 2^64 := by rw [length]; exact s.regs.rcx.toBitVec.isLt
  have ibound : i < 2^64 := by omega
  have targetDone := hc.targets ("delimited_u582", 582) (by decide)
  have targetLoop := hc.targets ("delimited_u240", 240) (by decide)
  have lenword : s.regs.rcx.toBitVec = BitVec.ofNat 64 data.size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact length.symm
  simp only [scanState]
  delimited_step 55 using hc
  delimited_step 56 using hc
  simp only [UInt64.toBitVec_ofNat']
  by_cases last : i = data.size
  · simpa [last, lenword, StatusFlags.from_result, targetDone, scanState, Effects.All]
      using done last _
  · have less : i < data.size := by omega
    have unequal : s.regs.rcx.toBitVec ≠ BitVec.ofNat 64 i := by
      intro equal
      have hn := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ibound,
        UInt64.toNat_toBitVec] at hn
      omega
    simp [StatusFlags.from_result, unequal, Effects.All]
    delimited_step 57 using hc
    simp only [UInt64.toBitVec_ofNat']
    delimited_load (bytes i less)
    delimited_step 58 using hc
    delimited_step 59 using hc
    by_cases hz : data[i]?.getD 0 = 0
    · simpa [hz, targetLoop, scanState, StatusFlags.from_result, Effects.All,
        UInt64.ofNat_add, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofNat_add]
        using zero less hz _
    · have hb : (data[i]?.getD 0).toBitVec ≠ 0#8 := by
        intro he
        apply hz
        exact UInt8.toBitVec_inj.1 he
      simpa [hb, scanState, StatusFlags.from_result, Effects.All,
        UInt64.ofNat_add, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofNat_add]
        using nonzero less hz _

/-- No fixed scan bound: the induction measure is the unread suffix length. -/
theorem scan_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes)
    (length : data.size = s.regs.rcx.toNat)
    (bytes : UintCodec.Large.BytesAt s.dmem s.regs.rdx.toBitVec data)
    (P : MachineState → Prop) :
    ∀ remaining i, i + remaining = data.size → ∀ flags,
    ((∀ j, i ≤ j → j < data.size → data[j]?.getD 0 = 0) → ∀ flags,
      Eventually (step e) P (scanState s data.size flags, base + 582)) →
    ((∃ j, i ≤ j ∧ j < data.size ∧ data[j]?.getD 0 ≠ 0) → ∀ j flags,
      Eventually (step e) P (scanState s j flags, base + 259)) →
    Eventually (step e) P (scanState s i flags, base + 240) := by
  intro remaining
  induction remaining with
  | zero =>
    intro i hi flags hz hn
    have he : i = data.size := by omega
    apply scan_iteration e base hc s data i flags length (by omega) bytes P
    · intro _ fl
      subst i
      exact hz (by intro j hj hlt; omega) fl
    · intro hlt
      omega
    · intro hlt
      omega
  | succ remaining ih =>
    intro i hi flags hz hn
    have less : i < data.size := by omega
    apply scan_iteration e base hc s data i flags length (by omega) bytes P
    · intro he
      omega
    · intro _ zero fl
      apply ih (i+1) (by omega) fl
      · intro all fl'
        apply hz _ fl'
        intro j hj hlt
        by_cases first : j = i
        · simpa only [first] using zero
        · exact all j (by omega) hlt
      · intro witness j fl'
        apply hn _ j fl'
        obtain ⟨k, hk, hlt, hnz⟩ := witness
        exact ⟨k, by omega, hlt, hnz⟩
    · intro _ nonzero fl
      exact hn ⟨i, Nat.le_refl i, less, nonzero⟩ (i+1) fl

end SszX86.Delimited
