import SszX86.DispatchBitListResources

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem bitList_owned (s : MachineData) (base : Int64) (ra : BitVec 64)
    (limit : Nat) (pointer payload : BitVec 64) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : Owned s base .bitList ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) limit)
    (pointer_load : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payload_load : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (payload.toNat : Int)) :
    SszX86.BitList.ListOwned (bodyState s base .bitList) (saved s ra)
      limit pointer payload data address capacity used := by
  have lp : Mem.loadInt (savedMem s) (s.regs.rsi.toBitVec + 8) 8 = some (pointer.toNat : Int) := by
    have same := (repr.header.subrange 0 8 (by decide)).load h.stack_low
    simp only [Nat.add_zero, ← UInt64.toNat_toBitVec, width_address] at same
    exact same.trans pointer_load
  have ln : Mem.loadInt (savedMem s) (s.regs.rsi.toBitVec + 16) 8 = some (payload.toNat : Int) := by
    have same := (repr.header.subrange 8 8 (by decide)).load h.stack_low
    simp only [Nat.add_assoc, Nat.reduceAdd, ← UInt64.toNat_toBitVec, width_address] at same
    exact same.trans payload_load
  refine {
    toOwned := bitList_resources s base false ra data address capacity used h
    pointer_load := lp
    payload_load := ln
    cap_pair := ?_
    borrowed := ?_ }
  · apply NatMemory.pair_of_at _ pointer payload limit (s.regs.rsi.toNat + 8)
      (repr.represented h.stack_low)
    · simpa only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
        show (8 : BitVec 64) = 8#64 by decide, Option.map_some, Int.toNat_natCast] using
        congrArg (Option.map Int.toNat) lp
    · simpa only [Nat.add_assoc, Nat.reduceAdd, widthLoad, ← UInt64.toNat_toBitVec,
        width_address, show (16 : BitVec 64) = 16#64 by decide, Option.map_some, Int.toNat_natCast] using
        congrArg (Option.map Int.toNat) ln
  · intro limbs stored
    exact (repr.large_protected h.stack_low pointer.toNat limbs stored).bitList h.stack_low false

theorem progressive_owned (s : MachineData) (base : Int64) (ra : BitVec 64)
    (limit : Option Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .progressiveBitList ra data address capacity used)
    (repr : OptionOwned s address capacity used (s.regs.rsi.toNat + 8) limit) :
    SszX86.BitList.ProgressiveOwned (bodyState s base .progressiveBitList) (saved s ra)
      limit data address capacity used := by
  refine {
    toOwned := bitList_resources s base true ra data address capacity used h
    option_at := repr.represented h.stack_low
    borrowed := ?_ }
  intro cap selected p limbs stored
  have storedNat : NatMemory.largeAt (widthLoad (savedMem s)) (s.regs.rsi.toNat + 8 + 8) p limbs := by
    simpa only [body_memory, body_descriptor, Nat.add_assoc, Nat.reduceAdd] using stored
  exact ((repr.payload cap selected).large_protected h.stack_low p limbs storedNat).bitList
    (base := base) (kind := .progressiveBitList) h.stack_low true

end SszX86.Dispatch
