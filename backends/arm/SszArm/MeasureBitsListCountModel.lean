import SszArm.MeasureBitsListWork
import SszArm.MeasureBitsAllocConstructor

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open UintCodec (widthLoad)

def Schema.site : Schema → Alloc.Site
  | .bounded _ => .bounded
  | .progressive _ => .progressive

def countCall (s : ArmState) (args : Args) (bits : Packed) : SszNative.NatArithmetic.Outcome NatOperand :=
  SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
    (arenaOf s args).used bits.count

def countWrites (s : ArmState) (args : Args) (bits : Packed) : List Delimited.Span :=
  match (countCall s args bits).allocation with
  | none => []
  | some reservation => [(args.arena.toNat + 16, 8), (reservation.pointer, 16)]

def Schema.countExit (schema : Schema) (bits : Packed) : Nat :=
  match schema with
  | .bounded _ => 1712
  | .progressive _ => if (bits.count >>> (64 : Nat)).setWidth 64 = 0#64 then 716 else 1584

structure CountPost (s t : ArmState) (args : Args) (schema : Schema) (bits : Packed)
    (base : BitVec 64) (actual : NatOperand) : Prop where
  counted : (countCall s args bits).result = .ok actual
  pc : read_pc t = base + BitVec.ofNat 64 (schema.countExit bits)
  program : t.program = s.program
  error : read_err t = read_err s
  work : Work t args schema bits
  pointer : r (.GPR 21#5) t = actual.pointer
  payload : r (.GPR 24#5) t = actual.payload
  actualAt : actual.At (widthLoad t)
  cursor : (read_mem_bytes 8 (args.arena + 16#64) t).toNat = (countCall s args bits).used
  header : read_mem_bytes 8 args.arena t = read_mem_bytes 8 args.arena s ∧
    read_mem_bytes 8 (args.arena + 8#64) t = read_mem_bytes 8 (args.arena + 8#64) s
  written : NatDivision.WrittenAt (widthLoad t) (countCall s args bits)
  frame : Delimited.MemoryFrame (countWrites s args bits) s t
  registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem count_pair (count : BitVec 128) :
    (count >>> (64 : Nat)).setWidth 64 ++ count.setWidth 64 = count := by
  apply BitVec.eq_of_toNat_eq
  rw [NatToU128.append_toNat]
  have bound := count.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem count_small (count : BitVec 128)
    (high : (count >>> (64 : Nat)).setWidth 64 = 0#64) : count.toNat < 2^64 := by
  rw [← count_pair count, high, NatToU128.append_toNat]
  simpa using (count.setWidth 64).isLt

theorem count_call_small (s : ArmState) (args : Args) (bits : Packed)
    (high : (bits.count >>> (64 : Nat)).setWidth 64 = 0#64) :
    countCall s args bits = SszNative.NatArithmetic.unchanged (arenaOf s args).used
      (.ok (.small (bits.count.setWidth 64))) := by
  simp only [countCall, SszNative.NatArithmetic.fromWide, count_small bits.count high, ↓reduceIte]

theorem Work.allocator_wide {schema : Schema} {s : ArmState} {args : Args} {bits : Packed}
    (work : Work s args schema bits) : Alloc.wide schema.site s = bits.count := by
  have pair : r (.GPR 25#5) s ++ r (.GPR 26#5) s = bits.count := by
    rw [work.high, work.low]
    exact count_pair bits.count
  cases schema <;>
    simp only [Alloc.wide, Schema.site, Alloc.Site.highReg, Alloc.Site.lowReg] <;>
    with_unfolding_all exact pair

theorem Work.allocator_outcome {schema : Schema} {s : ArmState} {args : Args} {bits : Packed}
    (work : Work s args schema bits) : Alloc.outcome schema.site s = countCall s args bits := by
  simp only [Alloc.outcome, countCall, work.allocator_wide, Alloc.addressWord,
    Alloc.capacityWord, Alloc.usedWord, work.arena, arenaOf]

end SszArm.Measure.Bits.List
