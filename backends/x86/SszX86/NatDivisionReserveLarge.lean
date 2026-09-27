import SszX86.NatDivisionReserveGuard

namespace SszX86.NatDivision.Reservation.Large
open SszX86.NatDivision
open SszX86.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  address_load : Mem.loadInt s.dmem s.regs.r12.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 = some (used.toNat : Int)

/-- All live source, divisor, length, loop, output-save and stack registers survive. -/
def Frame (s t : MachineData) : Prop :=
  t.zmms = s.zmms ∧
  ∀ reg, reg ≠ .rcx → reg ≠ .rdi → reg ≠ .r9 → reg ≠ .r10 →
    reg ≠ .r11 → reg ≠ .r14 → reg ≠ .r15 →
    t.regs.get64 reg = s.regs.get64 reg

def reservedState (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  let start := SszNative.Arena.start address.toNat used.toNat
  let pointer := BitVec.ofNat 64 (address.toNat + start)
  let finish := BitVec.ofNat 64 (SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat)
  {s with
    dmem := Mem.storeInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 finish.toInt
    regs := {s.regs with
      rcx := 2305843009213693950
      rdi := UInt64.ofNat start
      r9 := UInt64.ofBitVec pointer
      r10 := UInt64.ofBitVec finish
      r11 := UInt64.ofBitVec used
      r14 := UInt64.ofBitVec address
      r15 := UInt64.ofBitVec (used + address)}
    status := flags}

def Post (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Frame s t.1 ∧
  ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.rax.toNat = none ∧
      t.2 = base + 205 ∧ t.1.dmem = s.dmem) ∨
    ∃ r, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.rax.toNat = some r ∧
      t.2 = base + 627 ∧ ∃ flags, t.1 = reservedState s address used flags)

macro "natdiv_large_reservation_frame" : tactic => `(tactic|
  (refine ⟨rfl, ?_⟩
   intro reg h1 h2 h3 h4 h5 h6 h7
   cases reg <;>
     simp_all [committed, flagged, ended, alignedState, addressed, lengthState, Reg64s.get64]))

private theorem word_eq (value : BitVec 64) (n : Nat) (h : value.toNat = n) :
    value = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The full count guard and reserve refine the exact shared arithmetic model.
No capacity sign assumption or successful-reservation premise is used. The
success frontier precedes every payload write; the error frontier precedes the
saved-output restore and common ScratchExhausted record. -/
theorem runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) (positive : 0 < s.regs.rax.toNat) :
    Eventually (step e) (Post s base address capacity used) (s, base + 160) := by
  have failure (h : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat s.regs.rax.toNat) :
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.rax.toNat = none :=
    (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ positive).2 h
  apply length_cps e base hc
  intro scratchDI scratch9 f0
  by_cases length : 8 * s.regs.rax.toNat < 2^63
  · rw [ite_eq_left length]
    have bytes : (s.regs.rax.toBitVec * 8#64).toNat = 8 * s.regs.rax.toNat := by
      simp only [BitVec.toNat_mul, UInt64.toNat_toBitVec]
      change (s.regs.rax.toNat * 8) % 2^64 = 8 * s.regs.rax.toNat
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    apply address_cps e base hc (lengthState s scratchDI scratch9 f0) address used
    · exact header.address_load
    · exact header.used_load
    intro f1
    by_cases ha : address.toNat + used.toNat < 2^64
    · have ha' : used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_left ha']
      have sum : (used + address).toNat = address.toNat + used.toNat := by
        rw [UintCodec.Arena.add_nat used address ha']
        omega
      apply rounding_cps e base hc
      intro f2
      simp only [flagged, addressed, sum]
      by_cases rounding : address.toNat + used.toNat + 7 < 2^64
      · rw [ite_eq_left rounding]
        have pad : (paddingWord (used + address)).toNat =
            SszNative.Arena.padding (address.toNat + used.toNat) := by
          rw [UintCodec.Arena.padding_nat _ (by rw [sum]; exact rounding), sum]
        have rounded : ((used + address + 7#64) &&& ~~~7#64) =
            BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat) := by
          apply word_eq
          have roundedNat := SszNative.Arena.mask_rounding (used + address)
            (by rw [sum]; exact rounding)
          change ((used + address + 7#64) &&& ~~~7#64).toNat =
            SszNative.Arena.aligned (used + address).toNat at roundedNat
          simpa only [sum, SszNative.Arena.start_pointer] using roundedNat
        apply alignment_cps e base hc
        intro f3
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
          apply end_cps e base hc
          intro f4
          simp only [alignedState, lengthState, bytes, start]
          by_cases finish : SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat < 2^64
          · have finish' : 8 * s.regs.rax.toNat + SszNative.Arena.start address.toNat used.toNat < 2^64 := by
              simpa [SszNative.Arena.finish, Nat.add_comm] using finish
            rw [ite_eq_left finish']
            have endNat : (s.regs.rax.toBitVec * 8#64 + (paddingWord (used + address) + used)).toNat =
                SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat := by
              rw [UintCodec.Arena.add_nat _ _ (by rw [bytes, start]; exact finish'), bytes, start]
              simp [SszNative.Arena.finish, Nat.add_comm]
            have endWord := word_eq _ _ endNat
            apply capacity_cps e base hc (capacity := capacity)
            · exact header.capacity_load
            intro f5
            simp only [flagged, ended, endNat]
            by_cases fits : SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat ≤ capacity.toNat
            · rw [ite_eq_left fits]
              have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat s.regs.rax.toNat :=
                ⟨length, ha, rounding, hs, finish, fits⟩
              have successful := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ positive
                ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                  SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat⟩).2 ⟨checks, rfl⟩
              apply commit_cps e base hc
              · exact ⟨_, header.used_load⟩
              apply Eventually.done
              refine ⟨?_, Or.inr ⟨_, successful, rfl, f5, ?_⟩⟩
              · natdiv_large_reservation_frame
              · rw [startWord] at endWord
                simp only [committed, reservedState, endWord, startWord, rounded,
                  UInt64.ofBitVec_ofNat, uint64_literal]
            · rw [ite_eq_right fits]
              apply Eventually.done
              refine ⟨?_, Or.inl ⟨failure (fun h => fits h.2.2.2.2.2), rfl, rfl⟩⟩
              natdiv_large_reservation_frame
          · have finish' : ¬ 8 * s.regs.rax.toNat + SszNative.Arena.start address.toNat used.toNat < 2^64 := by
              simpa [SszNative.Arena.finish, Nat.add_comm] using finish
            rw [ite_eq_right finish']
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (fun h => finish h.2.2.2.2.1), rfl, rfl⟩⟩
            natdiv_large_reservation_frame
        · have hs' : ¬ SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_right hs']
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (fun h => hs h.2.2.2.1), rfl, rfl⟩⟩
          natdiv_large_reservation_frame
      · rw [ite_eq_right rounding]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (fun h => rounding h.2.2.1), rfl, rfl⟩⟩
        natdiv_large_reservation_frame
    · have ha' : ¬ used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_right ha']
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (fun h => ha h.2.1), rfl, rfl⟩⟩
      natdiv_large_reservation_frame
  · rw [ite_eq_right length]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (fun h => length h.1), rfl, rfl⟩⟩
    natdiv_large_reservation_frame

/-- Both exact outcomes are available to the main division proof. -/
theorem reservation_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) (positive : 0 < s.regs.rax.toNat)
    (P : MachineState → Prop)
    (hp : ∀ st, Post s base address capacity used st → Eventually (step e) P st) :
    Eventually (step e) P (s, base + 160) := by
  exact eventually_trans (step e) (Post s base address capacity used) P _
    (runs e base hc s address capacity used header positive) hp

/-- Byte-exact source/output/stack preservation outside the committed used slot. -/
theorem reserved_frame (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) (p : BitVec 64)
    (outside : ∀ j < 8, p ≠ s.regs.r12.toBitVec + 16#64 + BitVec.ofNat 64 j) :
    (reservedState s address used flags).dmem.get? p = s.dmem.get? p := by
  apply memmove_store_lookup_outside
  intro j hj
  exact outside j (by simpa only [Int.toBytes_length] using hj)

/-- The success cursor is exactly the source model's finish, without a signed
capacity restriction. -/
theorem reserved_cursor (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags)
    (bound : SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat < 2^64) :
    BoolCodec.observe (reservedState s address used flags).dmem s.regs.r12.toBitVec 16 8 =
      some (SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat) := by
  simpa [reservedState, Nat.mod_eq_of_lt bound] using
    BoolCodec.observe_store64 s.dmem s.regs.r12.toBitVec 16
      (BitVec.ofNat 64 (SszNative.Arena.finish address.toNat used.toNat s.regs.rax.toNat))

end SszX86.NatDivision.Reservation.Large
