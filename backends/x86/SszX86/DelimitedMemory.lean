import SszX86.DelimitedMath
import SszDelimitedProofs

namespace SszX86.Delimited
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The complete main activation includes the lowering's 16-byte BSR save area.
The empty and final-zero paths have no activation writes at all. -/
def UsesActivation (data : Ssz.Bytes) : Prop :=
  0 < data.size ∧ data[data.size - 1]! ≠ 0

instance (data : Ssz.Bytes) : Decidable (UsesActivation data) := by
  unfold UsesActivation
  infer_instance

def activationBytes (data : Ssz.Bytes) : Nat := if UsesActivation data then 104 else 0

/-- Immutable regions may overlap one another and the already-used arena prefix.
Zero-length regions impose no exclusion on their unused pointers. -/
structure Protected (s : MachineData) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 76
  activation : Body.Apart p n (s.regs.rsp.toNat - 104) (activationBytes data)
  cursor : Body.Apart p n (s.regs.r8.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

/-- Initial physical ownership, not an execution or semantic hypothesis. -/
structure Owned (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) : Prop where
  output_bound : s.regs.rdi.toNat + 76 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  stack_low : UsesActivation data → 104 ≤ s.regs.rsp.toNat
  stack_mapped : UsesActivation data →
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 104) 104
  output_return : Body.Apart s.regs.rdi.toNat 76 s.regs.rsp.toNat 8
  output_stack : Body.Apart s.regs.rdi.toNat 76
    (s.regs.rsp.toNat - 104) (activationBytes data)
  option_at : NatMemory.OptionAt (widthLoad s.dmem) s.regs.rsi.toNat limit
  option_owned : Protected s data address capacity used s.regs.rsi.toNat 24
  borrowed : ∀ cap, limit = some cap → ∀ p words,
    NatMemory.largeAt (widthLoad s.dmem) (s.regs.rsi.toNat + 8) p words →
    Protected s data address capacity used p (8 * words.length)
  length : data.size = s.regs.rcx.toNat
  source : Large.BytesAt s.dmem s.regs.rdx.toBitVec data
  source_owned : Protected s data address capacity used s.regs.rdx.toNat data.size
  header_bound : s.regs.r8.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 76
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 104) (activationBytes data)
  arena_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rsp.toNat 8
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r8.toNat 24
  header_output : Body.Apart s.regs.r8.toNat 24 s.regs.rdi.toNat 76
  header_stack : Body.Apart s.regs.r8.toNat 24
    (s.regs.rsp.toNat - 104) (activationBytes data)
  cursor_return : Body.Apart (s.regs.r8.toNat + 16) 8 s.regs.rsp.toNat 8

/-- Exactly the output, actual activation, committed cursor, and the two newly
reserved limbs may change. Alignment padding is not writable under this frame. -/
def Frame (s : MachineData) (m : DataMem) (data : Ssz.Bytes)
    (reserved : Option Arena.Reservation) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 76 →
    Body.Outside a.toNat (s.regs.rsp.toNat - 104) (activationBytes data) →
    (∀ r, reserved = some r →
      Body.Outside a.toNat (s.regs.r8.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer 16) →
    m.get? a = s.dmem.get? a

structure Returned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec ra
  sp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx = s.regs.rbx
  rbp : t.1.regs.rbp = s.regs.rbp
  r12 : t.1.regs.r12 = s.regs.r12
  r13 : t.1.regs.r13 = s.regs.r13
  r14 : t.1.regs.r14 = s.regs.r14
  r15 : t.1.regs.r15 = s.regs.r15
  simd : t.1.zmms = s.zmms
  returnSlot : Mem.loadInt t.1.dmem s.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes ra))

structure Post (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  observed : SszNative.Delimited.ResultAt (widthLoad t.1.dmem)
    s.regs.rdi.toNat s.regs.rdx.toNat s.regs.rsi.toNat data
    (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩)
  prepared : SszNative.Delimited.Outcome.PreparedAt (widthLoad t.1.dmem)
    (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩)
  returned : Returned s ra t
  frame : Frame s t.1.dmem data
    (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation
  cursor : widthLoad t.1.dmem (s.regs.r8.toNat + 16) 8 =
    some (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).used

theorem allocation_bounds (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (r : Arena.Reservation)
    (hr : SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩ = some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
    address.toNat + used.toNat ≤ r.pointer ∧
    r.pointer + 16 = address.toNat + r.used ∧
    r.used ≤ capacity.toNat ∧ r.pointer + 16 ≤ 2^64 := by
  unfold SszNative.Delimited.allocation at hr
  split at hr
  · exact SszNative.Delimited.reservation_bounds address.toNat capacity.toNat used.toNat
      h.arena_bound h.arena_nonzero r hr
  · contradiction

theorem preserves_region (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (m : DataMem) (frame : Frame s m data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩))
    (p n : Nat) (hp : Protected s data address capacity used p n) :
    ∀ i < n, m.get? (BitVec.ofNat 64 (p+i)) = s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i hi
  have within : p+i < 2^64 := by have := hp.bound; omega
  apply frame
  · have apart := hp.output
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
    omega
  · have apart := hp.activation
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
    omega
  · intro r hr
    have apartHeader := hp.cursor
    have apartArena := hp.arena
    have bounds := allocation_bounds s limit data address capacity used ra h r hr
    have usedBound := h.used_bound
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
    constructor <;> omega

theorem preserves_load (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (m : DataMem) (frame : Frame s m data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩))
    (p n offset count : Nat) (hp : Protected s data address capacity used p n)
    (within : offset + count ≤ n) :
    widthLoad m (p + offset) count = widthLoad s.dmem (p + offset) count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [Nat.add_assoc] using
    preserves_region s limit data address capacity used ra h m frame p n hp
      (offset+i) (by omega)

theorem option_preserved (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (m : DataMem) (frame : Frame s m data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩)) :
    NatMemory.OptionAt (widthLoad m) s.regs.rsi.toNat limit := by
  have descriptor := preserves_load s limit data address capacity used ra h m frame
    s.regs.rsi.toNat 24
  have descriptorTag : widthLoad m s.regs.rsi.toNat 4 =
      widthLoad s.dmem s.regs.rsi.toNat 4 := by
    simpa only [Nat.add_zero] using descriptor 0 4 h.option_owned (by decide)
  cases limit with
  | none =>
    exact descriptorTag.trans h.option_at
  | some cap =>
    obtain ⟨tag, nat⟩ := h.option_at
    refine ⟨?_, ?_⟩
    · exact descriptorTag.trans tag
    rcases nat with ⟨small, bound⟩ | ⟨p, words, large, value⟩
    · apply Or.inl
      refine ⟨?_, bound⟩
      simpa only [NatMemory.smallAt, Nat.add_assoc,
        descriptor 8 8 h.option_owned (by decide),
        descriptor 16 8 h.option_owned (by decide)] using small
    · apply Or.inr
      refine ⟨p, words, ?_, value⟩
      obtain ⟨pos, bound, align, room, pointer, count, limbs⟩ := large
      refine ⟨pos, bound, align, room, ?_, ?_, ?_⟩
      · rw [descriptor 8 8 h.option_owned (by decide)]
        exact pointer
      · simpa only [Nat.add_assoc, Nat.reduceAdd,
          descriptor 16 8 h.option_owned (by decide)] using count
      · intro i
        rw [preserves_load s (.some cap) data address capacity used ra h m frame
          p (8 * words.length) (8 * i.val) 8 (h.borrowed cap rfl p words
            ⟨pos, bound, align, room, pointer, count, limbs⟩) (by omega)]
        exact limbs i

end SszX86.Delimited
