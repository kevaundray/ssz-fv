import SszX86.UintArenaExec

namespace SszX86.UintCodec.Arena
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The only memory read by this prefix is the three-word caller arena header.
The used-word load also supplies the mapped destination needed by the commit.
There is deliberately no allocation-payload mapping assumption. -/
structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  nonwrap : s.regs.rbx.toBitVec.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.rbx.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 16#64) 8 = some (used.toNat : Int)

/-- Registers never modified by preparation or reservation, including all
caller pointers which remain live at either endpoint. -/
def Frame (s t : MachineData) : Prop :=
  t.regs.rdi = s.regs.rdi ∧ t.regs.rdx = s.regs.rdx ∧
  t.regs.rsp = s.regs.rsp ∧ t.regs.rbp = s.regs.rbp ∧
  t.regs.r12 = s.regs.r12 ∧ t.regs.r13 = s.regs.r13 ∧
  t.regs.r15 = s.regs.r15 ∧ t.zmms = s.zmms

theorem frame_refl (s : MachineData) : Frame s s := by simp [Frame]

theorem frame_trans {s t v : MachineData} (h : Frame s t) (h' : Frame t v) : Frame s v := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  rcases h' with ⟨h1',h2',h3',h4',h5',h6',h7',h8'⟩
  exact ⟨h1'.trans h1,h2'.trans h2,h3'.trans h3,h4'.trans h4,
    h5'.trans h5,h6'.trans h6,h7'.trans h7,h8'.trans h8⟩

theorem add_nat (a b : BitVec 64) (h : a.toNat + b.toNat < 2^64) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem padding_nat (a : BitVec 64) (h : a.toNat + 7 < 2^64) :
    (paddingWord a).toNat = SszNative.Arena.padding a.toNat := by
  have hm := SszNative.Arena.mask_rounding a h
  change ((a + 7#64) &&& ~~~7#64).toNat = SszNative.Arena.aligned a.toNat at hm
  have hb := SszNative.Arena.aligned_bounds a.toNat
  have hle : a ≤ (a + 7#64) &&& ~~~7#64 := by
    change a.toNat ≤ ((a + 7#64) &&& ~~~7#64).toNat
    rw [hm]
    exact hb.1
  rw [paddingWord, BitVec.toNat_sub_of_le hle, hm]
  rfl

theorem words_positive (count : Nat) (h : 0 < count) :
    0 < SszNative.Arena.wordsForBytes count := by
  simp [SszNative.Arena.wordsForBytes, Nat.ne_of_gt h]
  omega

theorem words_minus_one (count : Nat) (h : 0 < count) :
    SszNative.Arena.wordsForBytes count - 1 = (count - 1) / 8 := by
  simp [SszNative.Arena.wordsForBytes, Nat.ne_of_gt h]

/-- Exact arithmetic of SHR 3 on count-1, with arbitrary natural widths. -/
theorem prepare_words (s : MachineData) (count : Nat)
    (hn : 9 ≤ count) (hb : count < 2^63)
    (ht : s.regs.r10.toBitVec = BitVec.ofNat 64 (count - 1)) :
    s.regs.r10.toBitVec >>> 3 =
      BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count - 1) := by
  rw [ht, words_minus_one count (by omega)]
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h1 : count - 1 < 2^64 := by omega
  have h2 : (count - 1) / 8 < 2^64 := by omega
  simp [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

/-- The scaled LEA cannot overflow usize under the source-length bound, but
may still set the isize sign bit for counts greater than 2^63-8. -/
theorem prepare_bytes (s : MachineData) (count : Nat)
    (hn : 9 ≤ count) (hb : count < 2^63)
    (ht : s.regs.r10.toBitVec = BitVec.ofNat 64 (count - 1)) :
    (8#64 + (s.regs.r10.toBitVec >>> 3) * 8#64).toNat =
      8 * SszNative.Arena.wordsForBytes count := by
  rw [prepare_words s count hn hb ht]
  have hp := words_positive count (by omega)
  have hl := SszNative.Arena.wordsForBytes_bytes_lt count hb
  have hm : SszNative.Arena.wordsForBytes count - 1 < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hm]
  simp only [Nat.reducePow, Nat.reduceMod]
  have hmul : (SszNative.Arena.wordsForBytes count - 1) * 8 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt hmul]
  have hsum : 8 + (SszNative.Arena.wordsForBytes count - 1) * 8 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt hsum]
  omega

/-- In particular the lowered TEST/JL rejects exactly the upper seven
admissible byte counts; this is not approximated by a successful-reserve premise. -/
theorem isize_iff (count : Nat) (hn : 0 < count) :
    8 * SszNative.Arena.wordsForBytes count < 2^63 ↔ count ≤ 2^63 - 8 := by
  rw [SszNative.Arena.wordsForBytes_eq]
  omega

def cursorMemory (s : MachineData) (used : Nat) : DataMem :=
  Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 16#64) 8 (BitVec.ofNat 64 used).toInt

/-- Exact final register image at .LBB93_221 (5647), before its first CMP. -/
def packingState (s : MachineData) (count : Nat) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (BitVec.ofNat 64
        (SszNative.Arena.finish address.toNat used.toNat (SszNative.Arena.wordsForBytes count)))
      rcx := UInt64.ofBitVec (BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat))
      rsi := s.regs.r14
      r8 := UInt64.ofBitVec (BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count))
      r9 := UInt64.ofBitVec (BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat))
      r10 := UInt64.ofBitVec (BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count - 1))
      r11 := 0
      rbx := s.regs.rbp
      r14 := 0}
    status := flags
    dmem := cursorMemory s
      (SszNative.Arena.finish address.toNat used.toNat (SszNative.Arena.wordsForBytes count))}

theorem packing_frame (s : MachineData) (count : Nat) (address used : BitVec 64)
    (flags : StatusFlags) : Frame s (packingState s count address used flags) := by
  simp [Frame, packingState]

/-- The complete packing ABI, including both the retained count and the
decremented word count. RDI/RDX/RSP preservation is `packing_frame`. -/
theorem packing_registers (s : MachineData) (count : Nat) (address used : BitVec 64)
    (flags : StatusFlags) (hn : s.regs.rbp.toBitVec = BitVec.ofNat 64 count) :
    let t := packingState s count address used flags
    t.regs.r9.toBitVec =
        BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat) ∧
      t.regs.r8.toBitVec = BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count) ∧
      t.regs.r10.toBitVec = BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count - 1) ∧
      t.regs.rsi = s.regs.r14 ∧ t.regs.r11 = 0 ∧
      t.regs.rbx.toBitVec = BitVec.ofNat 64 count ∧
      t.regs.rbp.toBitVec = BitVec.ofNat 64 count ∧ t.regs.r14 = 0 := by
  simp [packingState, hn]

theorem cursor_observe (s : MachineData) (used : Nat) (hb : used < 2^64) :
    BoolCodec.observe (cursorMemory s used) s.regs.rbx.toBitVec 16 8 = some used := by
  simpa [cursorMemory, Nat.mod_eq_of_lt hb] using
    BoolCodec.observe_store64 s.dmem s.regs.rbx.toBitVec 16 (BitVec.ofNat 64 used)

/-- Byte-exact frame: every address outside the eight used-slot bytes is
unchanged, including source, stack and output whenever disjoint from that slot. -/
theorem cursor_frame (s : MachineData) (used : Nat) (p : BitVec 64)
    (hd : ∀ j < 8, p ≠ s.regs.rbx.toBitVec + 16#64 + BitVec.ofNat 64 j) :
    (cursorMemory s used).get? p = s.dmem.get? p := by
  apply memmove_store_lookup_outside
  intro j hj
  exact hd j (by simpa only [Int.toBytes_length] using hj)

/-- Both read-only header fields survive the commit. -/
theorem cursor_header (s : MachineData) (used : Nat)
    (hb : s.regs.rbx.toBitVec.toNat + 24 ≤ 2^64)
    (offset : Nat) (ho : offset = 0 ∨ offset = 8) :
    Mem.loadInt (cursorMemory s used) (s.regs.rbx.toBitVec + BitVec.ofNat 64 offset) 8 =
      Mem.loadInt s.dmem (s.regs.rbx.toBitVec + BitVec.ofNat 64 offset) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj he
  rw [memmove_addr_add, memmove_addr_add] at he
  have h := memmove_addr_injective s.regs.rbx.toBitVec 24 (offset+i) (16+j) hb
    (by rcases ho with rfl | rfl <;> omega) (by omega) he
  rcases ho with rfl | rfl <;> omega

end SszX86.UintCodec.Arena
