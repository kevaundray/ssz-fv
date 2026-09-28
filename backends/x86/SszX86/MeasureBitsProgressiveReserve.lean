import SszX86.MeasureBitsProgressiveReserveExec

namespace SszX86.Measure.ProgressiveReservation
open SszNative UintCodec

structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  address_load : Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 16#64) 8 = some (used.toNat : Int)

def Ready (s : MachineData) (address used : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r9 := UInt64.ofBitVec address
      rsi := UInt64.ofNat (SszNative.Arena.start address.toNat used.toNat)
      rdi := UInt64.ofNat (SszNative.Arena.start address.toNat used.toNat + 16)
      r8 := UInt64.ofBitVec (used + address)}
    status := flags}

structure Frame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  registers : ∀ reg, reg ≠ .r9 → reg ≠ .rsi → reg ≠ .rdi → reg ≠ .r8 →
    t.regs.get64 reg = s.regs.get64 reg

def Post (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Frame s t.1 ∧
  ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none ∧
      t.2 = base + 2963) ∨
    ∃ r, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r ∧
      t.2 = base + 1498 ∧ ∃ flags, t.1 = Ready s address used flags)

macro "measure_bits_progressivereservation_frame" : tactic => `(tactic|
  (refine ⟨rfl, rfl, ?_⟩
   intro reg h1 h2 h3 h4
   cases reg <;> simp_all [Ready, flagged, ended, alignedState, addressed, Reg64s.get64]))

private theorem word_eq (value : BitVec 64) (n : Nat) (h : value.toNat = n) :
    value = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Every checked addition, alignment and unsigned capacity test is executed.
No allocation-success hypothesis is used. -/
theorem runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) :
    Eventually (step e) (Post s base address capacity used) (s, base + 1425) := by
  have failure (h : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2) :
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none :=
    (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ 2 (by decide)).2 h
  have sixteen : (16 : BitVec 64).toNat = 16 := by decide
  apply address_cps e base hc s address used header.address_load header.used_load
  intro f0
  by_cases ha : address.toNat + used.toNat < 2^64
  · have ha' : used.toNat + address.toNat < 2^64 := by omega
    rw [ite_eq_left ha']
    have sum : (used + address).toNat = address.toNat + used.toNat := by
      rw [UintCodec.Arena.add_nat used address ha']
      omega
    apply rounding_cps e base hc
    intro f1
    simp only [flagged, addressed, sum]
    by_cases rounding : address.toNat + used.toNat + 7 < 2^64
    · rw [ite_eq_left rounding]
      have pad : (paddingWord (used + address)).toNat =
          SszNative.Arena.padding (address.toNat + used.toNat) := by
        rw [UintCodec.Arena.padding_nat _ (by rw [sum]; exact rounding), sum]
      apply alignment_cps e base hc
      intro f2
      simp only [pad]
      by_cases hs : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have hs' : SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
          simpa [SszNative.Arena.start, Nat.add_comm] using hs
        rw [ite_eq_left hs']
        have start : (paddingWord (used + address) + used).toNat =
            SszNative.Arena.start address.toNat used.toNat := by
          rw [UintCodec.Arena.add_nat _ _ (by rw [pad]; exact hs'), pad]
          simp [SszNative.Arena.start, Nat.add_comm]
        have startWord := word_eq _ _ start
        apply end_guard_cps e base hc
        intro f3
        simp only [flagged, alignedState, start]
        by_cases finish : SszNative.Arena.start address.toNat used.toNat + 16 < 2^64
        · rw [ite_eq_left finish]
          apply end_cps e base hc
          have endNat : ((paddingWord (used + address) + used) + (16 : BitVec 64)).toNat =
              SszNative.Arena.start address.toNat used.toNat + 16 := by
            rw [UintCodec.Arena.add_nat _ _ (by simpa only [start, sixteen] using finish), start, sixteen]
          have endWord := word_eq _ _ endNat
          apply capacity_cps e base hc (capacity := capacity)
          · exact header.capacity_load
          intro f4
          simp only [flagged, ended, endNat]
          by_cases fits : SszNative.Arena.start address.toNat used.toNat + 16 ≤ capacity.toNat
          · rw [ite_eq_left fits]
            have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2 :=
              ⟨by decide, ha, rounding, hs, finish, fits⟩
            have successful := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide)
              ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                SszNative.Arena.start address.toNat used.toNat + 16⟩).2 ⟨checks, rfl⟩
            apply Eventually.done
            refine ⟨?_, Or.inr ⟨_, successful, rfl, f4, ?_⟩⟩
            · measure_bits_progressivereservation_frame
            · rw [startWord] at endWord
              simp only [Ready, startWord, endWord, UInt64.ofBitVec_ofNat, Delimited.uint64_literal]
          · rw [ite_eq_right fits]
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (fun h => fits h.2.2.2.2.2), rfl⟩⟩
            measure_bits_progressivereservation_frame
        · rw [ite_eq_right finish]
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (fun h => finish h.2.2.2.2.1), rfl⟩⟩
          measure_bits_progressivereservation_frame
      · have hs' : ¬ SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
          simpa [SszNative.Arena.start, Nat.add_comm] using hs
        rw [ite_eq_right hs']
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (fun h => hs h.2.2.2.1), rfl⟩⟩
        measure_bits_progressivereservation_frame
    · rw [ite_eq_right rounding]
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (fun h => rounding h.2.2.1), rfl⟩⟩
      measure_bits_progressivereservation_frame
  · have ha' : ¬ used.toNat + address.toNat < 2^64 := by omega
    rw [ite_eq_right ha']
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (fun h => ha h.2.1), rfl⟩⟩
    measure_bits_progressivereservation_frame

end SszX86.Measure.ProgressiveReservation
