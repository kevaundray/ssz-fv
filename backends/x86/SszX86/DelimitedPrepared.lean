import SszX86.DelimitedMemory
import SszX86.DelimitedPrologue

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Live ABI facts after the prologue. Saved words come from the actual PUSHes;
the original input and output anchors are independent of volatile temporaries. -/
structure Active (s t : MachineData) (data : Ssz.Bytes) : Prop where
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 88
  out : t.regs.rdi = s.regs.rdi
  source : t.regs.rdx = s.regs.rdx
  length : t.regs.rcx = UInt64.ofNat data.size
  preceding : t.regs.r13 = UInt64.ofNat (data.size - 1)
  highest : t.regs.rbx = UInt64.ofNat (Ssz.highestBit data[data.size - 1]!)
  saved : SavedAt t.dmem t.regs.rsp.toBitVec s
  simd : t.zmms = s.zmms
  output : OutputMapped t
  stack : Large.Mapped t.dmem (s.regs.rsp.toBitVec - 104) 104

/-- The shared from_u128 result, with the actual committed memory and the words
that survive the optional comparison. The comparison's pointer is supplied at
its concrete R8/RSI edge rather than pretending a volatile register survives. -/
structure Ready (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (ready : SszNative.Delimited.Prepared) : Prop where
  active : Active s t data
  prepared : SszNative.Delimited.prepare ⟨address.toNat, capacity.toNat, used.toNat⟩
    (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)) = some ready
  allocation : SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
    ready.allocation
  low : t.regs.r14.toBitVec = ready.count.low
  high : t.regs.rbp.toBitVec = ready.count.high
  payload : t.regs.r15.toBitVec = BitVec.ofNat 64 ready.payload
  stored : SszNative.Delimited.PreparedAt (widthLoad t.dmem) ready
  cursor : widthLoad t.dmem (s.regs.r8.toNat + 16) 8 = some ready.used
  frame : Frame s t.dmem data ready.allocation

theorem Ready.model {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (state : Ready s t limit data address capacity used ready)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0) :
    SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
      SszNative.Delimited.finish limit data.size (Ssz.highestBit data[data.size - 1]!) ready := by
  rw [SszNative.Delimited.run_valid limit data _ nonempty delimiter, state.prepared]

theorem Ready.pair {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (h : Owned s limit data address capacity used ra)
    (state : Ready s t limit data address capacity used ready) :
    SszNative.NatMemory.Pair (widthLoad t.dmem) (BitVec.ofNat 64 ready.pointer)
      (BitVec.ofNat 64 ready.payload) ready.count.value :=
  SszNative.Delimited.PreparedAt.pair (widthLoad t.dmem)
    ⟨address.toNat, capacity.toNat, used.toNat⟩ _ ready state.prepared state.stored
    h.arena_bound h.arena_nonzero

theorem Ready.option {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (h : Owned s limit data address capacity used ra)
    (state : Ready s t limit data address capacity used ready) :
    SszNative.NatMemory.OptionAt (widthLoad t.dmem) s.regs.rsi.toNat limit := by
  apply option_preserved s limit data address capacity used ra h t.dmem
  simpa only [state.allocation] using state.frame

/-- Return-slot ownership follows from physical separation of the mutable
regions; immutable arena-header words may still alias the return slot. -/
theorem return_protected (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra) :
    Protected s data address capacity used s.regs.rsp.toNat 8 := by
  refine ⟨h.return_bound, h.output_return.symm, ?_, h.cursor_return.symm, h.arena_return.symm⟩
  by_cases active : UsesActivation data
  · have low := h.stack_low active
    simp only [activationBytes, ite_eq_left active, Body.Apart]
    omega
  · simp only [activationBytes, ite_eq_right active, Body.Apart]
    exact Or.inr (Or.inl True.intro)

theorem frame_return_load (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (m : DataMem)
    (frame : Frame s m data (SszNative.Delimited.allocation data
      ⟨address.toNat, capacity.toNat, used.toNat⟩)) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have same : Mem.loadInt m s.regs.rsp.toBitVec 8 = Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
    apply memmove_loadInt_congr
    intro i hi
    have byte := preserves_region s limit data address capacity used ra h m frame
      s.regs.rsp.toNat 8 (return_protected s limit data address capacity used ra h) i hi
    simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using byte
  exact same.trans h.return_load

theorem frame_source (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (m : DataMem)
    (frame : Frame s m data (SszNative.Delimited.allocation data
      ⟨address.toNat, capacity.toNat, used.toNat⟩)) :
    SszNative.ByteView.BytesAt (widthLoad m) s.regs.rdx.toNat data := by
  intro i hi
  rw [preserves_load s limit data address capacity used ra h m frame
    s.regs.rdx.toNat data.size i 1 h.source_owned (by omega)]
  simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
    h.source i hi, Option.map_some, Int.toNat_natCast]

end SszX86.Delimited
