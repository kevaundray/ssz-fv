import SszX86.EmitBitsCopy
import SszX86.EmitBitsFinish
import SszX86.EmitBitsMask

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open UintCodec BoolCodec
open BitVector (constructLow)

def stable (t : MachineData) :=
  (t.regs.rsp, t.regs.rbx, t.regs.r14, t.regs.r12, t.regs.r13,
    t.regs.rbp, t.regs.r15, t.zmms, t.dmem)

/-- Dead scratch registers and flags may vary freely between native tail
instructions. Borrowed memory, copied prefix and all live anchors stay exact. -/
theorem Copied.of_stable {s t u : MachineData} {bits : Packed} {src : BitVec 64}
    {size : Nat} {list : Bool} (copied : Copied s t bits src size list)
    (same : stable u = stable t) : Copied s u bits src size list := by
  simp only [stable, Prod.mk.injEq] at same
  rcases same with ⟨hsp, hbx, hout, hsrc, hfull, hsaved, hcapacity, hvector, hmem⟩
  exact ⟨hsp.trans copied.stack, hbx.trans copied.result, hout.trans copied.output,
    by simpa only [hsrc] using copied.source,
    by simpa only [hfull] using copied.full,
    by simpa only [hsaved] using copied.saved,
    hcapacity.trans copied.capacity, hvector.trans copied.vector,
    by simpa only [hmem] using copied.prefix,
    by simpa only [hmem] using copied.frame,
    by simpa only [hmem] using copied.mapping,
    by simpa only [hmem] using copied.low,
    by simpa only [hmem] using copied.length⟩

theorem Copied.full_nat {s t : MachineData} {bits : Packed} {src : BitVec 64}
    {size : Nat} {list : Bool} (copied : Copied s t bits src size list)
    (physical : bits.bytes.size < 2^64) : t.regs.r13.toNat = bits.count.toNat / 8 := by
  have backing := (backing_guards bits).1
  have bound : bits.count.toNat / 8 < 2^64 := by omega
  simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    using congrArg BitVec.toNat copied.full

theorem Copied.saved_nat {s t : MachineData} {bits : Packed} {src : BitVec 64}
    {size : Nat} {list : Bool} (copied : Copied s t bits src size list)
    (physical : bits.bytes.size < 2^64) :
    t.regs.rbp.toNat = if list then bits.count.toNat % 8 else bits.bytes.size := by
  have bound : (if list then bits.count.toNat % 8 else bits.bytes.size) < 2^64 := by
    cases list <;> simp_all
    omega
  simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    using congrArg BitVec.toNat copied.saved

theorem Copied.byte_load {s t : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} {list : Bool}
    (owned : Owned s desc bits src size) (copied : Copied s t bits src size list)
    (nonaligned : bits.count.toNat % 8 ≠ 0) :
    Mem.loadInt t.dmem (t.regs.r12.toBitVec + t.regs.r13.toBitVec) 1 =
      some ((bits.bytes[bits.count.toNat / 8]!).toNat : Int) := by
  have backing := (backing_guards bits).2.2 nonaligned
  have inside : bits.count.toNat / 8 < bits.bytes.size := by omega
  have stored : t.dmem.get? (src + BitVec.ofNat 64 (bits.count.toNat / 8)) =
      some bits.bytes[bits.count.toNat / 8] :=
    owned.source_at copied.frame (bits.count.toNat / 8) inside
  have lookup : t.dmem.get? (src + BitVec.ofNat 64 (bits.count.toNat / 8)) =
      some bits.bytes[bits.count.toNat / 8]! := by
    simpa only [getElem!_pos bits.bytes (bits.count.toNat / 8) inside] using stored
  rw [copied.source, copied.full]
  exact SszX86.Emit.Bits.byte_load t.dmem (src + BitVec.ofNat 64 (bits.count.toNat / 8))
    bits.bytes[bits.count.toNat / 8]! lookup

theorem Copied.result_load {s t : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} {list : Bool}
    (owned : Owned s desc bits src size) (copied : Copied s t bits src size list) :
    ∃ old, Mem.loadInt t.dmem t.regs.rbx.toBitVec 8 = some old := by
  rw [copied.result]
  simpa only [BitVec.add_zero] using Large.mapped_load t.dmem s.regs.rbx.toBitVec 8 0 8
    (copied.mapping _ _ owned.resultMapped) (by decide)

theorem Copied.tail_load {s t : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} {list : Bool}
    (owned : Owned s desc bits src size) (copied : Copied s t bits src size list)
    (inside : bits.count.toNat / 8 < size) :
    ∃ old, Mem.loadInt t.dmem (t.regs.r14.toBitVec + t.regs.r13.toBitVec) 1 = some old := by
  rw [copied.output, copied.full]
  exact Large.mapped_load t.dmem s.regs.r14.toBitVec size (bits.count.toNat / 8) 1
    (copied.mapping _ _ owned.outputMapped) (by omega)

end SszX86.Emit.Bits
