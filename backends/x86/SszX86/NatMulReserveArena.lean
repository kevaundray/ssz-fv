import SszX86.NatMulReserveGuard

namespace SszX86.NatMul.Reservation
open SszX86.Delimited

structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  address_load : Mem.loadInt s.dmem s.regs.r9.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 = some (used.toNat : Int)

def Frame (s t : MachineData) : Prop :=
  t.zmms = s.zmms ∧
  ∀ reg, reg ≠ .rdx → reg ≠ .r8 → reg ≠ .r11 → reg ≠ .r14 →
    reg ≠ .r15 → reg ≠ .rbx → t.regs.get64 reg = s.regs.get64 reg

def reservedState (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  let start := SszNative.Arena.start address.toNat used.toNat
  {s with
    regs := {s.regs with
      rdx := UInt64.ofNat (8 * s.regs.r14.toNat)
      r8 := UInt64.ofNat start
      r11 := UInt64.ofNat (start + 8 * s.regs.r14.toNat)
      r15 := UInt64.ofBitVec address
      rbx := UInt64.ofBitVec (used + address)}
    status := flags}

def GuardPost (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Frame s t.1 ∧
  ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.r14.toNat = none ∧
      t.2 = base + 318 ∧ t.1.dmem = s.dmem) ∨
    ∃ r, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.r14.toNat = some r ∧
      t.2 = base + 444 ∧ ∃ flags, t.1 = reservedState s address used flags)

macro "natmul_reservation_frame" : tactic => `(tactic|
  (refine ⟨rfl, ?_⟩
   intro reg h1 h2 h3 h4 h5 h6
   cases reg <;>
     simp_all [flagged, ended, alignedState, addressed, lengthState, Reg64s.get64]))

private theorem word_eq (value : BitVec 64) (n : Nat) (h : value.toNat = n) :
    value = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Exact positive-length reserve, with all unsigned guards, from the completed
maximum/count-overflow cut. Inputs, output pointer, arena pointer, and RSP survive. -/
theorem guards_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) (positive : 0 < s.regs.r14.toNat) :
    Eventually (step e) (GuardPost s base address capacity used) (s, base + 287) := by
  have failure (h : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
      s.regs.r14.toNat) :
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
        s.regs.r14.toNat = none :=
    (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by omega)).2 h
  apply length_cps e base hc
  intro scratch8 scratch11 f0
  by_cases length : 8 * s.regs.r14.toNat < 2^63
  · rw [ite_eq_left length]
    have bytes : (s.regs.r14.toBitVec * 8#64).toNat =
        8 * s.regs.r14.toNat := by
      have overflow : 8 * s.regs.r14.toNat < 2^64 := by omega
      have expr : (s.regs.r14.toBitVec * 8#64).toNat =
          (8 * s.regs.r14.toNat) % 2^64 := by
        simp [BitVec.toNat_mul, Nat.mul_mod, Nat.mul_comm]
      rw [expr, Nat.mod_eq_of_lt overflow]
    have bytesWord := word_eq _ _ bytes
    apply address_cps e base hc (lengthState s scratch8 scratch11 f0)
      address used header.address_load header.used_load
    intro f1
    by_cases ha : address.toNat + used.toNat < 2^64
    · have ha' : used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_left ha']
      have sum : (used + address).toNat = address.toNat + used.toNat := by
        rw [UintCodec.Arena.add_nat used address ha']
        omega
      apply rounding_cps e base hc
      intro f2
      simp only [flagged, addressed, lengthState, sum]
      by_cases rounding : address.toNat + used.toNat + 7 < 2^64
      · rw [ite_eq_left rounding]
        have pad : (paddingWord (used + address)).toNat =
            SszNative.Arena.padding (address.toNat + used.toNat) := by
          rw [UintCodec.Arena.padding_nat _ (by rw [sum]; exact rounding), sum]
        apply alignment_cps e base hc
        intro f3
        simp only [pad, UInt64.toNat_ofBitVec]
        by_cases hs : SszNative.Arena.start address.toNat used.toNat < 2^64
        · have hs' : SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_left hs']
          have start : (paddingWord (used + address) + used).toNat =
              SszNative.Arena.start address.toNat used.toNat := by
            rw [UintCodec.Arena.add_nat _ _ (by rw [pad]; exact hs'), pad]
            simp [SszNative.Arena.start, Nat.add_comm]
          have startWord := word_eq _ _ start
          apply end_cps e base hc
          intro f4
          simp only [ended, alignedState, bytes, start]
          by_cases finish : SszNative.Arena.start address.toNat used.toNat +
              8 * s.regs.r14.toNat < 2^64
          · rw [ite_eq_left finish]
            have endNat : ((paddingWord (used + address) + used) +
                (s.regs.r14.toBitVec * 8#64)).toNat =
                SszNative.Arena.start address.toNat used.toNat +
                  8 * s.regs.r14.toNat := by
              rw [UintCodec.Arena.add_nat _ _ (by rw [start, bytes]; exact finish), start, bytes]
            have endWord := word_eq _ _ endNat
            apply capacity_cps e base hc (capacity := capacity)
            · exact header.capacity_load
            intro f5
            simp only [flagged, endNat]
            by_cases fits : SszNative.Arena.start address.toNat used.toNat +
                8 * s.regs.r14.toNat ≤ capacity.toNat
            · rw [ite_eq_left fits]
              have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
                  s.regs.r14.toNat := ⟨length, ha, rounding, hs, finish, fits⟩
              have successful := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega)
                ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                  SszNative.Arena.start address.toNat used.toNat +
                    8 * s.regs.r14.toNat⟩).2 ⟨checks, rfl⟩
              apply Eventually.done
              refine ⟨?_, Or.inr ⟨_, successful, rfl, f5, ?_⟩⟩
              · natmul_reservation_frame
              · simp only [reservedState, startWord, bytesWord, UInt64.ofBitVec_ofNat, uint64_literal]
                congr 2
                apply UInt64.toBitVec_inj.mp
                simpa only [startWord, bytesWord, UInt64.toBitVec_ofNat'] using endWord
            · rw [ite_eq_right fits]
              apply Eventually.done
              refine ⟨?_, Or.inl ⟨failure (fun h => fits h.2.2.2.2.2), rfl, rfl⟩⟩
              natmul_reservation_frame
          · rw [ite_eq_right finish]
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (fun h => finish h.2.2.2.2.1), rfl, rfl⟩⟩
            natmul_reservation_frame
        · have hs' : ¬ SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_right hs']
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (fun h => hs h.2.2.2.1), rfl, rfl⟩⟩
          natmul_reservation_frame
      · rw [ite_eq_right rounding]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (fun h => rounding h.2.2.1), rfl, rfl⟩⟩
        natmul_reservation_frame
    · have ha' : ¬ used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_right ha']
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (fun h => ha h.2.1), rfl, rfl⟩⟩
      natmul_reservation_frame
  · rw [ite_eq_right length]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (fun h => length h.1), rfl, rfl⟩⟩
    natmul_reservation_frame

end SszX86.NatMul.Reservation
