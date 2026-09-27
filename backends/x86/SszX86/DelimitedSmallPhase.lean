import SszX86.DelimitedCountPhase
import SszX86.DelimitedArenaCommit

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem Ready.with_status {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (state : Ready s t limit data address capacity used ready) (flags : StatusFlags) :
    Ready s {t with status := flags} limit data address capacity used ready := by
  have live := state.active
  refine ⟨⟨live.sp, live.out, live.source, live.length, live.preceding, live.highest,
    live.saved, live.simd, live.output, live.stack⟩, state.prepared, state.allocation,
    state.low, state.high, state.payload, state.stored, state.cursor, state.frame⟩

theorem prepared_allocation (limit : Option Nat) (data : Ssz.Bytes)
    (arena : SszNative.Delimited.ArenaState) (ready : SszNative.Delimited.Prepared)
    (physical : data.size < 2^64) (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (prepared : SszNative.Delimited.prepare arena
      (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)) = some ready) :
    SszNative.Delimited.allocation data arena = ready.allocation := by
  have resource := (SszNative.Delimited.run_resources limit data arena physical).1
  rw [SszNative.Delimited.run_valid limit data arena nonempty delimiter, prepared] at resource
  exact resource.symm

/-- A prefix with no reservation cannot touch the cursor, even when the cursor
or immutable header fields alias other readonly regions. -/
theorem noalloc_cursor (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (m : DataMem) (frame : Frame s m data none) :
    widthLoad m (s.regs.r8.toNat + 16) 8 = some used.toNat := by
  have same : widthLoad m (s.regs.r8.toNat + 16) 8 =
      widthLoad s.dmem (s.regs.r8.toNat + 16) 8 := by
    unfold widthLoad
    congr 1
    apply memmove_loadInt_congr
    intro i hi
    have bound := h.header_bound
    have within : s.regs.r8.toNat + 16 + i < 2^64 := by omega
    have position : (BitVec.ofNat 64 (s.regs.r8.toNat + 16) + BitVec.ofNat 64 i).toNat =
        s.regs.r8.toNat + 16 + i := by
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
    apply frame
    · rw [position]
      have apart := h.header_output
      unfold Body.Outside Body.Apart at *
      omega
    · rw [position]
      have apart := h.header_stack
      unfold Body.Outside Body.Apart at *
      omega
    · intro reservation impossible
      cases impossible
  rw [same]
  simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address]
  have current : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int) := by
    simpa only [BitVec.ofNat_eq_ofNat] using h.used_load
  rw [current]
  rfl

/-- Both linked Option loads inspect the only two valid input tags. -/
theorem ready_option_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (ready : SszNative.Delimited.Prepared) (state : Ready s t limit data address capacity used ready)
    (optionAddress : t.regs.rsi = s.regs.rsi)
    (pointer : t.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer)
    (P : MachineState → Prop)
    (hp : ∀ u, Ready s u limit data address capacity used ready → u.regs.rsi = s.regs.rsi →
      u.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer → Eventually (step e) P
        (u, if limit.isSome then base + 374 else base + 523)) :
    Eventually (step e) P (t, base + 139) ∧ Eventually (step e) P (t, base + 365) := by
  let tag : BitVec 32 := if limit.isSome then 1#32 else 0#32
  have observed : widthLoad t.dmem s.regs.rsi.toNat 4 = some tag.toNat := by
    have option := state.option h
    cases limit with
    | none => exact option
    | some cap => exact option.1
  have tagRead : Mem.loadInt t.dmem t.regs.rsi.toBitVec 4 = some (tag.toNat : Int) := by
    have native := widthLoad_eq t.dmem s.regs.rsi.toNat 4 tag.toNat observed
    simpa only [optionAddress, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using native
  have continuation : ∀ flags, Eventually (step e) P
      ({t with status := flags}, if tag = 1#32 then base + 374 else base + 523) := by
    intro flags
    have next := hp {t with status := flags} (state.with_status flags) optionAddress pointer
    cases limit <;> simpa only [tag, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, show (0#32) ≠ 1#32 by decide, ↓reduceIte] using next
  exact ⟨small_option_cps e base hc t tag tagRead P continuation,
    Reservation.option_cps e base hc t tag tagRead P continuation⟩

theorem small_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (state : Counted s t data) (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (small : (SszNative.Delimited.countWords data.size
      (Ssz.highestBit data[data.size - 1]!)).high = 0#64)
    (P : MachineState → Prop)
    (hp : ∀ u ready, Ready s u limit data address capacity used ready → u.regs.rsi = s.regs.rsi →
      u.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer → Eventually (step e) P
        (u, if limit.isSome then base + 374 else base + 523)) :
    Eventually (step e) P (t, base + 133) := by
  let count := SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)
  let ready : SszNative.Delimited.Prepared := ⟨count, used.toNat, none⟩
  have prepared : SszNative.Delimited.prepare ⟨address.toNat, capacity.toNat, used.toNat⟩ count =
      some ready := by simp only [SszNative.Delimited.prepare, count, small, ↓reduceIte, ready]
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
  have allocation := prepared_allocation limit data ⟨address.toNat, capacity.toNat, used.toNat⟩
    ready physical nonempty delimiter prepared
  apply small_count_cps e base hc
  intro flags
  let u : MachineData := {t with regs := {t.regs with r8 := 0, r15 := t.regs.r14}, status := flags}
  have live := state.active
  have active : Active s u data :=
    ⟨live.sp, live.out, live.source, live.length, live.preceding, live.highest,
      live.saved, live.simd, live.output, live.stack⟩
  have readyState : Ready s u limit data address capacity used ready := by
    refine ⟨active, prepared, allocation, state.low, state.high, ?_, small, ?_, state.frame⟩
    · change t.regs.r14.toBitVec = BitVec.ofNat 64 count.low.toNat
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using state.low
    · exact noalloc_cursor s limit data address capacity used ra h t.dmem state.frame
  apply (ready_option_cps e base hc s u limit data address capacity used ra h ready
    readyState state.optionAddress (by rfl) P _).1
  intro v valid option pointer
  exact hp v ready valid option pointer

end SszX86.Delimited
