import SszX86.CodecDecodeFixedReserveExec

namespace SszX86.CodecDecodeFixed
open SszX86.UintCodec
open SszNative

/-- Only the six literal allocator scratch registers may change at this cut. -/
def ValueReserveFrame (s t : MachineData) : Prop :=
  t.zmms = s.zmms ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r15 →
    t.regs.get64 r = s.regs.get64 r

def valueReservedState (s : MachineData) (arena address used : BitVec 64)
    (count : Nat) (flags : StatusFlags) : MachineData :=
  let start := TypedArena.start CodecDecode.valueLayout address.toNat used.toNat
  let finish := start + 48 * count
  {s with
    regs := {s.regs with
      rax := UInt64.ofNat finish
      rcx := UInt64.ofNat start
      rdx := UInt64.ofBitVec arena
      rsi := UInt64.ofBitVec (used + address)
      rdi := UInt64.ofBitVec address
      r15 := UInt64.ofNat (address.toNat + start)}
    status := flags
    dmem := Mem.storeInt s.dmem (arena + 16#64) 8 (BitVec.ofNat 64 finish).toInt}

def ValueReservationPost (s : MachineData) (base : Int64)
    (arena address capacity used : BitVec 64) (count : Nat) (t : MachineState) : Prop :=
  ValueReserveFrame s t.1 ∧
  ((TypedArena.reserve CodecDecode.valueLayout address.toNat capacity.toNat used.toNat count = none ∧
      t.2 = base + 77 ∧ t.1.dmem = s.dmem) ∨
    ∃ reservation,
      TypedArena.reserve CodecDecode.valueLayout address.toNat capacity.toNat used.toNat count = some reservation ∧
      reservation.pointer = address.toNat + TypedArena.start CodecDecode.valueLayout address.toNat used.toNat ∧
      reservation.used = TypedArena.start CodecDecode.valueLayout address.toNat used.toNat + 48 * count ∧
      t.2 = base + 351 ∧ ∃ flags, t.1 = valueReservedState s arena address used count flags)

macro "codec_value_reserve_frame" : tactic => `(tactic|
  (refine ⟨rfl, ?_⟩
   intro r h1 h2 h3 h4 h5 h6
   cases r <;> simp_all [reserveFlagged, reserveAddressed, reserveAligned,
     reserveEnded, reserveCapacity, valueReservedState, Reg64s.get64]))

private theorem reserve_word_eq (v : BitVec 64) (n : Nat) (h : v.toNat = n) :
    v = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The complete native PC260..347 specialized reserve<Value> chain, stopping
at PC351 after the cursor commit and before the first Value initializer. The
byte-product equality and isize guard are facts established by PC46..71; this
cut neither assumes a successful reservation nor initializes payload/padding. -/
theorem value_reserve_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (arena address capacity used : BitVec 64) (count : Nat)
    (header : ReserveHeader s arena address capacity used)
    (positive : 0 < count)
    (bytes : s.regs.rax.toNat = 48 * count)
    (isize : 48 * count < 2^63) :
    Eventually (step e) (ValueReservationPost s base arena address capacity used count)
      (s, base + 260) := by
  have failure (h : ¬TypedArena.Checks CodecDecode.valueLayout
      address.toNat capacity.toNat used.toNat count) :
      TypedArena.reserve CodecDecode.valueLayout address.toNat capacity.toNat used.toNat count = none := by
    rw [TypedArena.reserve_positive _ _ _ _ _ positive (by decide)]
    exact if_neg h
  apply reserve_address_cps e base hc s arena address capacity used header
  intro f0
  by_cases addressOk : address.toNat + used.toNat < 2^64
  · have addressOk' : used.toNat + address.toNat < 2^64 := by omega
    rw [ite_eq_left addressOk']
    have sum : (used + address).toNat = address.toNat + used.toNat := by
      rw [UintCodec.Arena.add_nat used address addressOk']
      omega
    apply reserve_rounding_cps e base hc
    intro f1
    simp only [reserveAddressed, UInt64.toNat_ofBitVec, sum]
    by_cases rounding : address.toNat + used.toNat + 15 < 2^64
    · rw [ite_eq_left rounding]
      have pad : (valuePaddingWord (used + address)).toNat =
          TypedArena.padding CodecDecode.valueLayout (address.toNat + used.toNat) := by
        rw [valuePaddingWord, value_padding _ (by rw [sum]; exact rounding), sum]
      have alignedNat : (((used + address + 15#64) &&& ~~~15#64)).toNat =
          address.toNat + TypedArena.start CodecDecode.valueLayout address.toNat used.toNat := by
        rw [value_mask_rounding _ (by rw [sum]; exact rounding), sum,
          TypedArena.start_pointer]
      have alignedWord := reserve_word_eq _ _ alignedNat
      apply reserve_alignment_cps e base hc
      intro f2
      simp only [reserveFlagged, reserveAddressed, UInt64.toNat_ofBitVec, pad]
      by_cases startOk : TypedArena.start CodecDecode.valueLayout address.toNat used.toNat < 2^64
      · have startOk' : TypedArena.padding CodecDecode.valueLayout (address.toNat + used.toNat) +
            used.toNat < 2^64 := by
          simpa only [TypedArena.start, Nat.add_comm] using startOk
        rw [ite_eq_left startOk']
        have startNat : (valuePaddingWord (used + address) + used).toNat =
            TypedArena.start CodecDecode.valueLayout address.toNat used.toNat := by
          rw [UintCodec.Arena.add_nat _ _ (by rw [pad]; exact startOk'), pad]
          simp only [TypedArena.start, Nat.add_comm]
        have startWord := reserve_word_eq _ _ startNat
        apply reserve_end_cps e base hc
        intro f3
        simp only [reserveAligned, reserveFlagged, reserveAddressed,
          UInt64.toNat_ofBitVec, bytes, startNat]
        by_cases endOk : TypedArena.start CodecDecode.valueLayout address.toNat used.toNat +
            48 * count < 2^64
        · have endOk' : 48 * count + TypedArena.start CodecDecode.valueLayout
              address.toNat used.toNat < 2^64 := by omega
          rw [ite_eq_left endOk']
          have endNat : (s.regs.rax.toBitVec + (valuePaddingWord (used + address) + used)).toNat =
              TypedArena.start CodecDecode.valueLayout address.toNat used.toNat + 48 * count := by
            rw [UintCodec.Arena.add_nat _ _ (by
              rw [startNat]
              change s.regs.rax.toNat + _ < _
              rw [bytes]
              exact endOk'), startNat]
            change s.regs.rax.toNat + _ = _
            omega
          have endWord := reserve_word_eq _ _ endNat
          apply reserve_capacity_cps e base hc (arena := arena) (capacity := capacity)
          · exact header.arena_load
          · exact header.capacity_load
          intro f4
          simp only [reserveEnded, reserveAligned, reserveFlagged, reserveAddressed,
            UInt64.toNat_ofBitVec, endNat]
          by_cases fits : TypedArena.start CodecDecode.valueLayout address.toNat used.toNat +
              48 * count ≤ capacity.toNat
          · rw [ite_eq_left fits]
            have checks : TypedArena.Checks CodecDecode.valueLayout
                address.toNat capacity.toNat used.toNat count :=
              ⟨isize, addressOk, rounding, startOk, endOk, fits⟩
            have success : TypedArena.reserve CodecDecode.valueLayout
                address.toNat capacity.toNat used.toNat count =
                some ⟨address.toNat + TypedArena.start CodecDecode.valueLayout address.toNat used.toNat,
                  TypedArena.start CodecDecode.valueLayout address.toNat used.toNat + 48 * count⟩ := by
              rw [TypedArena.reserve_positive _ _ _ _ _ positive (by decide), if_pos checks]
              rfl
            apply reserve_commit_cps e base hc
            · exact ⟨_, header.used_load⟩
            apply Eventually.done
            refine ⟨?_, Or.inr ⟨_, success, rfl, rfl, rfl, f4, ?_⟩⟩
            · codec_value_reserve_frame
            · simp only [reserveCapacity, reserveEnded, reserveAligned, reserveFlagged,
                reserveAddressed, valueReservedState, startWord, endWord, alignedWord]
          · rw [ite_eq_right fits]
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (by intro checks; exact fits checks.2.2.2.2.2), rfl, rfl⟩⟩
            codec_value_reserve_frame
        · have noEnd : ¬48 * count + TypedArena.start CodecDecode.valueLayout address.toNat used.toNat < 2^64 := by omega
          rw [ite_eq_right noEnd]
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (by intro checks; exact endOk checks.2.2.2.2.1), rfl, rfl⟩⟩
          codec_value_reserve_frame
      · have noStart : ¬TypedArena.padding CodecDecode.valueLayout (address.toNat + used.toNat) + used.toNat < 2^64 := by
          simpa only [TypedArena.start, Nat.add_comm] using startOk
        rw [ite_eq_right noStart]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (by intro checks; exact startOk checks.2.2.2.1), rfl, rfl⟩⟩
        codec_value_reserve_frame
    · rw [ite_eq_right rounding]
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (by intro checks; exact rounding checks.2.2.1), rfl, rfl⟩⟩
      codec_value_reserve_frame
  · have noAddress : ¬used.toNat + address.toNat < 2^64 := by omega
    rw [ite_eq_right noAddress]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (by intro checks; exact addressOk checks.2.1), rfl, rfl⟩⟩
    codec_value_reserve_frame

/-- A committed reservation leaves alignment gaps and the entire uninitialized
Value payload untouched. Only the arena used-word changes in this prefix. -/
theorem value_reserved_frame (s : MachineData) (arena address used : BitVec 64)
    (count : Nat) (flags : StatusFlags) (a : BitVec 64)
    (outside : ∀ i < 8, a ≠ arena + 16#64 + BitVec.ofNat 64 i) :
    (valueReservedState s arena address used count flags).dmem.get? a = s.dmem.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  exact outside i (by simpa only [Int.toBytes_length] using hi)

end SszX86.CodecDecodeFixed
