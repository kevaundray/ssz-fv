import SszX86.UintBodyMemory

namespace SszX86.UintCodec.Body
open Kraken.X64.Parser
open SszNative WordDecode BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Facts obtained at the Large frontier from width and trimming, not caller
premises about future register contents or memory. -/
structure LargeEntry (s u : MachineData) (data : Ssz.Bytes) (count : Nat) : Prop where
  anchors : Anchors s u
  memory : u.dmem = s.dmem
  arena : u.regs.rbx = s.regs.rbx
  source : u.regs.rdx = s.regs.rdx
  length : u.regs.r14.toNat = data.size
  hcount : u.regs.rbp.toBitVec = BitVec.ofNat 64 count
  pred : u.regs.r10.toBitVec = BitVec.ofNat 64 (count - 1)

structure ReservationFacts (address capacity used : BitVec 64) (count : Nat)
    (r : SszNative.Arena.Reservation) : Prop where
  pointer : r.pointer = address.toNat + SszNative.Arena.start address.toNat used.toNat
  cursor : r.used = SszNative.Arena.finish address.toNat used.toNat
    (SszNative.Arena.wordsForBytes count)
  positive : 0 < r.pointer
  aligned : r.pointer % 8 = 0
  inside : r.pointer + 8 * SszNative.Arena.wordsForBytes count ≤ address.toNat + capacity.toNat
  lower : address.toNat + used.toNat ≤ r.pointer
  pointer_bound : r.pointer < 2^64
  cursor_bound : r.used < 2^64
  fits : SszNative.Arena.start address.toNat used.toNat +
    8 * SszNative.Arena.wordsForBytes count ≤ capacity.toNat
  available : used.toNat < capacity.toNat

theorem reservation_facts (s : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (count : Nat) (hc : 0 < count) (r : SszNative.Arena.Reservation)
    (hr : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = some r) :
    ReservationFacts address capacity used count r := by
  have hw := Arena.words_positive count hc
  rcases (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ hw r).1 hr with ⟨checks, rfl⟩
  have fit := checks.2.2.2.2.2
  have cb := checks.2.2.2.2.1
  have ab := h.arena_bound
  have startLo := SszNative.Arena.used_le_start address.toNat used.toNat
  have ap : 0 < address.toNat := h.arena_nonzero (by
    unfold SszNative.Arena.finish at fit
    omega)
  have align : (address.toNat + SszNative.Arena.start address.toNat used.toNat) % 8 = 0 := by
    rw [SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  refine ⟨rfl, rfl, ?_, align, ?_, ?_, ?_, cb, ?_, ?_⟩
  all_goals
    try dsimp only
    unfold SszNative.Arena.finish at fit
    omega

theorem entry_header {s u : MachineData} {data : Ssz.Bytes} {count : Nat}
    {address capacity used : BitVec 64} (he : LargeEntry s u data count)
    (hh : Arena.Header s address capacity used) : Arena.Header u address capacity used := by
  rcases hh with ⟨hb, ha, hc, hu⟩
  exact ⟨by simpa only [he.arena] using hb,
    by simpa only [he.memory, he.arena] using ha,
    by simpa only [he.memory, he.arena] using hc,
    by simpa only [he.memory, he.arena] using hu⟩

/-- Cursor commits preserve arbitrary separately owned physical regions. -/
theorem cursor_region (u : MachineData) (used : Nat) (p : BitVec 64) (n : Nat)
    (hh : u.regs.rbx.toNat + 24 ≤ 2^64) (hp : p.toNat + n ≤ 2^64)
    (hd : Apart p.toNat n u.regs.rbx.toNat 24) :
    ∀ i < n, (Arena.cursorMemory u used).get? (p + BitVec.ofNat 64 i) =
      u.dmem.get? (p + BitVec.ofNat 64 i) := by
  intro i hi
  apply Arena.cursor_frame
  intro j hj
  unfold Apart at hd
  simp only [← UInt64.toNat_toBitVec] at hh hd
  bv_omega

theorem packing_tail (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (count : Nat) (he : LargeEntry s u data count) (flags : StatusFlags) :
    TailOwned (Arena.packingState u count address used flags) saved := by
  have hu := h.tail.same_memory he.anchors he.memory
  apply hu.transport (arena_anchors (Arena.packing_frame _ _ _ _ _))
  · intro i hi
    exact cursor_region u _ u.regs.rdi.toBitVec 80
      (by simpa only [he.arena, UInt64.toNat_toBitVec] using h.header.nonwrap)
      hu.separated.outputHigh
      (by simpa only [he.arena, he.anchors.out, UInt64.toNat_toBitVec] using h.header_output.symm) i hi
  · intro i hi
    exact cursor_region u _ u.regs.rsp.toBitVec 368
      (by simpa only [he.arena, UInt64.toNat_toBitVec] using h.header.nonwrap)
      hu.separated.stackHigh
      (by simpa only [he.arena, he.anchors.sp, UInt64.toNat_toBitVec] using h.header_stack.symm) i hi

theorem packing_frame (s u : MachineData) (data : Ssz.Bytes) (count : Nat)
    (address used : BitVec 64) (he : LargeEntry s u data count)
    (r : SszNative.Arena.Reservation) (flags : StatusFlags) :
    Frame s (Arena.packingState u count address used flags).dmem count (some r) := by
  intro a _ _ hr
  change (Arena.cursorMemory u _).get? a = _
  rw [Arena.cursor_frame]
  · rw [he.memory]
  · simpa only [he.arena] using (hr r rfl).1

/-- All packing preconditions follow from initial physical ownership and the
actual successful reservation. No intermediate memory contents are assumed. -/
theorem packing_ready (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (count : Nat) (hc : 9 ≤ count) (hle : count ≤ data.size)
    (he : LargeEntry s u data count) (r : SszNative.Arena.Reservation)
    (hr : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = some r) (flags : StatusFlags) :
    Large.Ready (Arena.packingState u count address used flags) data count := by
  have rf := reservation_facts s saved expectedWidth data address capacity used h count (by omega) r hr
  have regs := Arena.packing_registers u count address used flags he.hcount
  have ptrNat : (BitVec.ofNat 64
      (address.toNat + SszNative.Arena.start address.toNat used.toNat)).toNat = r.pointer := by
    rw [← rf.pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rf.pointer_bound]
  have length : u.regs.r14.toBitVec = BitVec.ofNat 64 data.size := by
    rw [← he.length]
    simp
  refine ⟨hc, hle, h.size, ?_, regs.2.2.2.2.2.1, regs.2.2.2.2.2.2.1,
    regs.2.1, regs.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Arena.packingState, Large.get, Reg64s.get64] using length
  · simp only [Arena.packingState, Large.get, Reg64s.get64]
    rfl
  · simp only [Arena.packingState, Large.get, Reg64s.get64]
    rfl
  · simpa only [Arena.packingState, Large.get, Reg64s.get64, UInt64.toBitVec_ofBitVec,
      ptrNat] using rf.positive
  · simpa only [Arena.packingState, Large.get, Reg64s.get64, UInt64.toBitVec_ofBitVec,
      ptrNat] using rf.aligned
  · simpa only [Arena.packingState, Large.get, Reg64s.get64, he.source, UInt64.toNat_toBitVec] using h.source_owned.bound
  · change (BitVec.ofNat 64 _).toNat + _ ≤ _
    rw [ptrNat]
    exact Nat.le_trans rf.inside h.arena_bound
  · intro i hi
    change Mem.loadInt (Arena.cursorMemory u _) (u.regs.rdx.toBitVec + BitVec.ofNat 64 i) 1 = _
    rw [show Mem.loadInt (Arena.cursorMemory u _) (u.regs.rdx.toBitVec + BitVec.ofNat 64 i) 1 =
        Mem.loadInt u.dmem (u.regs.rdx.toBitVec + BitVec.ofNat 64 i) 1 by
      apply memmove_loadInt_congr
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp only [BitVec.add_zero]
      apply Arena.cursor_frame
      intro k hk
      have hs := h.source_owned.bound
      have hd := h.source_owned.cursor
      have hh := h.header.nonwrap
      rw [he.source, he.arena]
      unfold Apart at hd
      simp only [← UInt64.toNat_toBitVec] at hs hd hh
      bv_omega]
    simpa only [he.memory, he.source] using h.source i hi
  · change Large.Mapped (Arena.cursorMemory u _)
      (BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat)) _
    apply Large.mapped_store
    intro i hi
    have hb : SszNative.Arena.start address.toNat used.toNat + i < capacity.toNat := by
      have := rf.fits
      omega
    have hm := h.arena_mapped (SszNative.Arena.start address.toNat used.toNat + i) hb
    simpa only [he.memory, width_address, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using hm
  · change Large.Disjoint u.regs.rdx.toBitVec
      (BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat)) _ _
    apply apart_bytes
    · simpa only [he.source, UInt64.toNat_toBitVec] using h.source_owned.bound
    · rw [ptrNat]
      exact Nat.le_trans rf.inside h.arena_bound
    · rw [ptrNat, he.source]
      have hd := h.source_owned.arena
      have hlo := rf.lower
      have hhi := rf.inside
      have hav := rf.available
      unfold Apart at *
      simp only [UInt64.toNat_toBitVec]
      omega

/-- A complete Large fill, with original activation ownership and the exact
cursor-plus-reserved-destination frame ready for the success tail. -/
theorem large_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s u : MachineData) (saved : Saved) (expectedWidth : Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s saved expectedWidth data address capacity used)
    (count : Nat) (hc : 9 ≤ count) (hle : count ≤ data.size)
    (he : LargeEntry s u data count) (r : SszNative.Arena.Reservation)
    (hr : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = some r)
    (hsig : count = significantBytes data data.size) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ t, Anchors s t → TailOwned t saved → Frame s t.dmem count (some r) →
      Cursor s t.dmem (some r) →
      Tail.NatPair t t.regs.r9.toBitVec t.regs.r8.toBitVec (Ssz.readUint data 0 data.size) →
      Eventually (step e) P (t, base + 5502)) :
    Eventually (step e) P (Arena.packingState u count address used flags, base + 5647) := by
  let p := Arena.packingState u count address used flags
  have ready := packing_ready s u saved expectedWidth data address capacity used h count hc hle he r hr flags
  have rf := reservation_facts s saved expectedWidth data address capacity used h count (by omega) r hr
  have hav := rf.available
  have wpos := Arena.words_positive count (by omega)
  have hpa : Anchors s p := he.anchors.trans (arena_anchors (Arena.packing_frame _ _ _ _ _))
  have hpo : TailOwned p saved := packing_tail s u saved expectedWidth data address capacity used h count he flags
  have hpf : Frame s p.dmem count (some r) := packing_frame s u data count address used he r flags
  have pp : p.regs.r9.toBitVec = BitVec.ofNat 64 r.pointer := by
    simp only [p, Arena.packingState, UInt64.toBitVec_ofBitVec, rf.pointer]
  have ppn : p.regs.r9.toNat = r.pointer := by
    change p.regs.r9.toBitVec.toNat = _
    rw [pp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rf.pointer_bound]
  have destOut : Apart p.regs.r9.toNat (8 * SszNative.Arena.wordsForBytes count) s.regs.rdi.toNat 80 := by
    rw [ppn]
    have hd := h.arena_output
    have hlo := rf.lower
    have hhi := rf.inside
    unfold Apart at *
    omega
  have destStack : Apart p.regs.r9.toNat (8 * SszNative.Arena.wordsForBytes count) s.regs.rsp.toNat 368 := by
    rw [ppn]
    have hd := h.arena_stack
    have hlo := rf.lower
    have hhi := rf.inside
    unfold Apart at *
    omega
  have cursor0 : Cursor s p.dmem (some r) := by
    intro v hv
    have eq : r = v := Option.some.inj hv
    subst v
    change widthLoad (Arena.cursorMemory u _) (s.regs.rbx.toNat + 16) 8 = some r.used
    rw [← rf.cursor]
    change widthLoad (Arena.cursorMemory u r.used) (s.regs.rbx.toBitVec.toNat + 16) 8 = _
    simpa only [widthLoad, width_address, BoolCodec.observe, he.arena] using
      Arena.cursor_observe u r.used rf.cursor_bound
  apply eventually_trans _ _ _ _ (Large.fills_significant e base code p data count ready hsig)
  intro st hst
  rcases hst with ⟨res, value⟩
  have cursor : Cursor s st.1.dmem (some r) := by
    intro v hv
    have eq : Mem.loadInt st.1.dmem (BitVec.ofNat 64 (s.regs.rbx.toNat + 16)) 8 =
        Mem.loadInt p.dmem (BitVec.ofNat 64 (s.regs.rbx.toNat + 16)) 8 := by
      apply memmove_loadInt_congr
      intro i hi
      apply res.frame
      intro j hj
      change _ ≠ p.regs.r9.toBitVec + BitVec.ofNat 64 j
      have hb := h.header.nonwrap
      have hd := h.arena_header
      have hlo := rf.lower
      have hhi := rf.inside
      have hbound := h.arena_bound
      have hptr := rf.pointer_bound
      rw [pp]
      unfold Apart at hd
      simp only [← UInt64.toNat_toBitVec] at hb hd ⊢
      bv_omega
    simpa only [widthLoad, eq] using cursor0 v hv
  have anchors := hpa.trans (large_anchors res.fixed)
  have own : TailOwned st.1 saved := by
    apply hpo.transport (large_anchors res.fixed)
    · intro i hi
      apply res.frame
      intro j hj
      have hb := ready.destination_bound
      have ho := h.tail.separated.outputHigh
      change p.regs.r9.toNat + 8 * SszNative.Arena.wordsForBytes count ≤ 2^64 at hb
      have hd := destOut
      rw [hpa.out]
      unfold Apart at hd
      change s.regs.rdi.toBitVec + BitVec.ofNat 64 i ≠ p.regs.r9.toBitVec + BitVec.ofNat 64 j
      simp only [← UInt64.toNat_toBitVec] at hb ho hd
      bv_omega
    · intro i hi
      apply res.frame
      intro j hj
      have hb := ready.destination_bound
      have ho := h.tail.separated.stackHigh
      change p.regs.r9.toNat + 8 * SszNative.Arena.wordsForBytes count ≤ 2^64 at hb
      have hd := destStack
      rw [hpa.sp]
      unfold Apart at hd
      change s.regs.rsp.toBitVec + BitVec.ofNat 64 i ≠ p.regs.r9.toBitVec + BitVec.ofNat 64 j
      simp only [← UInt64.toNat_toBitVec] at hb ho hd
      bv_omega
  have frame : Frame s st.1.dmem count (some r) := by
    intro a ho hw hr'
    exact (res.frame a (by simpa only [Large.get, Reg64s.get64, pp] using (hr' r rfl).2)).trans
      (hpf a ho hw hr')
  have pair : Tail.NatPair st.1 st.1.regs.r9.toBitVec st.1.regs.r8.toBitVec
      (Ssz.readUint data 0 data.size) := by
    have nw := SszNative.Arena.wordsForBytes_bytes_lt count (by have := h.size; omega)
    have plen : (decodeWords data 0 count).length = SszNative.Arena.wordsForBytes count := by
      simp only [decodeWords_length, SszNative.Arena.wordsForBytes_eq]
    have pr : st.1.regs.r9.toBitVec = p.regs.r9.toBitVec := res.pointer
    refine Or.inr ⟨decodeWords data 0 count, ?_, ?_, ?_, ?_, ?_, value, Or.inr ⟨?_, ?_⟩⟩
    · rw [pr]
      exact ready.pointer_nonzero
    · rw [pr]
      exact ready.pointer_aligned
    · rw [pr, plen]
      exact ready.destination_bound
    · have words : st.1.regs.r8.toBitVec = BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count) := res.words
      rw [words, plen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · simpa only [Large.get, Reg64s.get64, pr] using res.contents
    · have hd := destOut
      rw [pr, plen, anchors.out]
      simp only [UInt64.toNat_toBitVec]
      unfold Apart at hd
      omega
    · have hd := destStack
      rw [pr, plen, anchors.sp]
      simp only [UInt64.toNat_toBitVec]
      unfold Apart at hd
      omega
  rcases st with ⟨t, pc⟩
  simp only at res anchors own frame cursor pair
  have hpc : pc = base + 5502 := res.pc
  rw [hpc]
  exact hp t anchors own frame cursor pair

end SszX86.UintCodec.Body
