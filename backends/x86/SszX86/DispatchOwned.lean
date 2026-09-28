import SszX86.DispatchJump
import SszX86.BitVectorMemory
import SszX86.BitListMemory

namespace SszX86.Dispatch
open BoolCodec UintCodec SszNative

/-- Physical entry-SP coordinates. The deepest primitive helper reaches 472
bytes below entrySP; the original return word remains at entrySP. -/
def stackStart (s : MachineData) : Nat := s.regs.rsp.toNat - 472

structure ReadOnly (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 80
  stack : Body.Apart p n (stackStart s) 472
  cursor : Body.Apart p n (s.regs.r8.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

/-- All fields observe the original function-entry register file and memory.
No saved activation, dispatched state, helper ownership or future result occurs
in these premises. Read-only spans may alias each other and the used arena. -/
structure Owned (s : MachineData) (base : Int64) (kind : Kind) (ra : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64) : Prop where
  stack_low : 472 ≤ s.regs.rsp.toNat
  stack_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  stack_mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 472) 480
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  output_bound : s.regs.rdi.toNat + 80 ≤ 2^64
  output_mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 80
  output_stack : Body.Apart s.regs.rdi.toNat 80 (stackStart s) 480
  tag : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (kind.tag : Int)
  descriptor_owned : ReadOnly s address capacity used s.regs.rsi.toNat
    (if kind = .progressiveBitList then 32 else 24)
  table : TableAt s.dmem base
  table_owned : ReadOnly s address capacity used (tableAddress base).toNat tableBytes.length
  length : data.size = s.regs.rcx.toNat
  source : Large.BytesAt s.dmem s.regs.rdx.toBitVec data
  source_owned : ReadOnly s address capacity used s.regs.rdx.toNat data.size
  header_bound : s.regs.r8.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16) 8 = some (used.toNat : Int)
  header_stack : Body.Apart s.regs.r8.toNat 24 (stackStart s) 480
  header_output : Body.Apart s.regs.r8.toNat 24 s.regs.rdi.toNat 80
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 80
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (stackStart s) 480
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r8.toNat 24

theorem ReadOnly.subrange {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (h : ReadOnly s address capacity used p n)
    (off count : Nat) (within : off + count ≤ n) :
    ReadOnly s address capacity used (p + off) count := by
  rcases h with ⟨hb, ho, hs, hc, ha⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> unfold Body.Apart at * <;> omega

private theorem scalar_pushes (sp : BitVec 64) (p n : Nat)
    (bound : p + n ≤ 2^64) (low : 472 ≤ sp.toNat)
    (apart : Body.Apart p n (sp.toNat - 472) 472) :
    ∀ i < n, ∀ j < 48,
      BitVec.ofNat 64 p + BitVec.ofNat 64 i ≠ sp - 48 + BitVec.ofNat 64 j := by
  intro i hi j hj
  have srcBound : p + i < 2^64 := by omega
  have srcNat : (BitVec.ofNat 64 p + BitVec.ofNat 64 i).toNat = p + i := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt srcBound]
  have subNat : (sp - 48).toNat = sp.toNat - 48 := by
    exact BitVec.toNat_sub_of_le (by change 48 ≤ sp.toNat; omega)
  have indexBound : j < 2^64 := by omega
  have dstBound : sp.toNat - 48 + j < 2^64 := by have := sp.isLt; omega
  have dstNat : (sp - 48 + BitVec.ofNat 64 j).toNat = sp.toNat - 48 + j := by
    rw [BitVec.toNat_add, subNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt indexBound, Nat.mod_eq_of_lt dstBound]
  intro same
  have sameNat := congrArg BitVec.toNat same
  rw [srcNat, dstNat] at sameNat
  unfold Body.Apart at apart
  omega

theorem ReadOnly.pushes {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) :
    ∀ i < n, ∀ j < 48,
      BitVec.ofNat 64 p + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j := by
  apply scalar_pushes _ p n h.bound
  · simpa only [← UInt64.toNat_toBitVec] using low
  · rw [UInt64.toNat_toBitVec]
    exact h.stack

theorem ReadOnly.load {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) :
    Mem.loadInt (savedMem s) (BitVec.ofNat 64 p) n =
      Mem.loadInt s.dmem (BitVec.ofNat 64 p) n := saved_load s _ n (h.pushes low)

theorem ReadOnly.width {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) :
    widthLoad (savedMem s) p n = widthLoad s.dmem p n := by
  unfold widthLoad
  rw [h.load low]

theorem body_spNat (s : MachineData) (base : Int64) (kind : Kind)
    (low : 472 ≤ s.regs.rsp.toNat) :
    (bodyState s base kind).regs.rsp.toNat = s.regs.rsp.toNat - 360 := by
  change (bodyState s base kind).regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec.toNat - 360
  rw [body_sp]
  change 472 ≤ s.regs.rsp.toBitVec.toNat at low
  bv_omega

theorem Owned.push_mapped {s : MachineData} {base : Int64} {kind : Kind} {ra : BitVec 64}
    {data : Ssz.Bytes} {address capacity used : BitVec 64}
    (h : Owned s base kind ra data address capacity used) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
  intro i hi
  have hm := h.stack_mapped (424 + i) (by omega)
  clear h
  have translated : s.regs.rsp.toBitVec - 472 + BitVec.ofNat 64 (424 + i) =
      s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 i := by
    bv_omega
  rw [translated] at hm
  exact hm

theorem entry_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : Kind) (ra : BitVec 64) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (h : Owned s base kind ra data address capacity used)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (bodyState s base kind, base + Int64.ofNat kind.entry)) :
    Eventually (step e) P (s, base) := by
  apply setup_runs e base hc s kind P h.push_mapped h.tag
  · have desc := h.descriptor_owned.subrange 0 8 (by split <;> decide)
    simpa only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ← UInt64.toNat_toBitVec] using desc.pushes h.stack_low
  apply jump_runs e base hc s kind P
  · apply saved_table s base h.table
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.table_owned.pushes h.stack_low
  · exact next

end SszX86.Dispatch
