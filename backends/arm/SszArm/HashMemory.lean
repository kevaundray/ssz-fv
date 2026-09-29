import SszArm.HashContract
import SszArm.HashTableSize

namespace SszArm.Hash

open Delimited (Span Protected MemoryFrame)

theorem vectorByteArray_size {n : Nat} (bytes : Vector UInt8 n) :
    (ByteArray.mk bytes.toArray).size = n := by
  rw [← ByteArray.size_data]
  exact bytes.size_toArray

theorem initialByteArray_size : (ByteArray.mk initialTable.toArray).size = 32 := by
  rw [← ByteArray.size_data]
  change initialTable.toArray.size = 32
  rw [List.size_toArray]
  rfl

theorem roundsByteArray_size : (ByteArray.mk roundsTable.toArray).size = 256 := by
  rw [← ByteArray.size_data]
  change roundsTable.toArray.size = 256
  rw [List.size_toArray]
  exact roundsTable_length

theorem protected_subspan {writes : List Span} {address bytes inner count : Nat}
    (owned : Protected writes address bytes) (lo : address ≤ inner)
    (hi : inner + count ≤ address + bytes) : Protected writes inner count := by
  rcases owned with empty | separate
  · left; omega
  · right
    intro span member
    have apart := separate span member
    omega

theorem frame_mono {small large : List Span} {s t : ArmState}
    (frame : MemoryFrame small s t)
    (contained : ∀ span ∈ small, ∃ outer ∈ large,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2) :
    MemoryFrame large s t := by
  intro address outside
  apply frame
  intro span member
  obtain ⟨outer, memberOuter, lo, hi⟩ := contained span member
  have apart := outside outer memberOuter
  omega

theorem read_frame {writes : List Span} {s t : ArmState} (address : BitVec 64) (bytes : Nat)
    (frame : MemoryFrame writes s t) (physical : address.toNat + bytes ≤ 2^64)
    (owned : Protected writes address.toNat bytes) :
    read_mem_bytes bytes address t = read_mem_bytes bytes address s := by
  apply BoolCodec.read_bytes_congr
  intro i bound
  change t.mem _ = s.mem _
  apply frame
  intro span member
  rcases owned with empty | separate
  · omega
  · have apart := separate span member
    bv_omega

theorem bytesAt_frame {writes : List Span} {s t : ArmState} {address : BitVec 64}
    {bytes : ByteArray} (frame : MemoryFrame writes s t)
    (physical : address.toNat + bytes.size ≤ 2^64)
    (owned : Protected writes address.toNat bytes.size) (source : BytesAt s address bytes) :
    BytesAt t address bytes := by
  intro i
  rw [frame (address + BitVec.ofNat 64 i.val) (by
    intro span member
    rcases owned with empty | separate
    · have bound := i.isLt; omega
    · have apart := separate span member
      have bound := i.isLt
      bv_omega)]
  exact source i

theorem ChainingAt.frame {writes : List Span} {s t : ArmState} {address : BitVec 64}
    {words : Vector UInt32 8} (source : ChainingAt s address words)
    (frame : MemoryFrame writes s t) (physical : address.toNat + 32 ≤ 2^64)
    (owned : Protected writes address.toNat 32) : ChainingAt t address words := by
  intro i
  have bound := i.isLt
  have addressNat : (address + BitVec.ofNat 64 (4 * i.val)).toNat = address.toNat + 4 * i.val := by
    bv_omega
  rw [read_frame _ 4 frame (by rw [addressNat]; omega) (by
    rw [addressNat]
    exact protected_subspan owned (by omega) (by omega))]
  exact source i

theorem StateAt.frame {writes : List Span} {s t : ArmState} {address : BitVec 64}
    {value : StreamState} (source : StateAt s address value)
    (frame : MemoryFrame writes s t) (physical : address.toNat + 112 ≤ 2^64)
    (owned : Protected writes address.toNat 112) : StateAt t address value := by
  have at64 : (address + 64#64).toNat = address.toNat + 64 := by bv_omega
  have at96 : (address + 96#64).toNat = address.toNat + 96 := by bv_omega
  have at104 : (address + 104#64).toNat = address.toNat + 104 := by bv_omega
  constructor
  · exact bytesAt_frame frame (by rw [vectorByteArray_size]; omega)
      (by rw [vectorByteArray_size]; exact protected_subspan owned (Nat.le_refl _) (by omega)) source.buffer
  · exact source.chaining.frame frame (by rw [at64]; omega)
      (by rw [at64]; exact protected_subspan owned (by omega) (by omega))
  · rw [read_frame _ 8 frame (by rw [at96]; omega)
      (by rw [at96]; exact protected_subspan owned (by omega) (by omega))]
    exact source.buffered
  · rw [read_frame _ 8 frame (by rw [at104]; omega)
      (by rw [at104]; exact protected_subspan owned (by omega) (by omega))]
    exact source.byteLen

theorem DataAt.frame {writes : List Span} {s t : ArmState} {base : BitVec 64}
    (data : DataAt s base) (frame : MemoryFrame writes s t)
    (initial : Protected writes (base + initialOffset).toNat 32)
    (rounds : Protected writes (base + roundsOffset).toNat 256) : DataAt t base := by
  constructor
  · exact bytesAt_frame frame (by rw [initialByteArray_size]; exact data.initialBound)
      (by rw [initialByteArray_size]; exact initial) data.initial
  · exact bytesAt_frame frame (by rw [roundsByteArray_size]; exact data.roundsBound)
      (by rw [roundsByteArray_size]; exact rounds) data.rounds
  · exact data.initialBound
  · exact data.roundsBound

/-- Real memcpy, including V0 clobber and its original LR return. -/
theorem memcpy_correct (s : ArmState) (base : BitVec 64) (bytes : ByteArray)
    (code : CodeAt s base) (pc : read_pc s = base + memcpyOffset)
    (error : read_err s = .None)
    (dstBound : (r (.GPR 0#5) s).toNat + bytes.size ≤ 2^64)
    (srcBound : (r (.GPR 1#5) s).toNat + bytes.size ≤ 2^64)
    (sep : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) bytes.size)
    (length : (r (.GPR 2#5) s).toNat = bytes.size)
    (source : BytesAt s (r (.GPR 1#5) s) bytes) :
    let t := run (Memcpy.fuel bytes.size) s
    Returned s t ∧ BytesAt t (r (.GPR 0#5) s) bytes ∧
      MemoryFrame [((r (.GPR 0#5) s).toNat, bytes.size)] s t := by
  arm_word_nf at dstBound srcBound sep length source ⊢
  have correct := Memcpy.program_correct s (base + memcpyOffset) code.memcpy pc error
    (by arm_word_nf; simpa only [length] using dstBound)
    (by arm_word_nf; simpa only [length] using srcBound)
    (by arm_word_nf; simpa only [length] using sep)
  arm_word_nf at correct
  simp only [length] at correct
  rcases correct with ⟨err, ret, _, prog, regs, memory⟩
  refine ⟨⟨ret, err, prog, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact regs (.GPR 31#5) (by simp [Memcpy.Preserved])
  · intro reg lo hi
    apply regs
    simp only [Memcpy.Preserved]
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor <;> bv_omega
  · intro reg lo hi
    rw [regs (.SFP reg) (by simp only [Memcpy.Preserved]; bv_omega)]
  · intro i
    have bound := i.isLt
    have addressNat : (r (.GPR 0#5) s + BitVec.ofNat 64 i.val).toNat =
        (r (.GPR 0#5) s).toNat + i.val := by bv_omega
    arm_word_nf at addressNat
    rw [memory, Memcpy.image, if_pos (by rw [addressNat]; omega)]
    rw [addressNat, Nat.add_sub_cancel_left]
    exact source i
  · intro address outside
    rw [memory, Memcpy.image, if_neg (by
      have apart := outside ((r (.GPR 0#5) s).toNat, bytes.size) (by simp)
      omega)]

/-- Real memset: its SIMD scratch register is not included in the ABI frame. -/
theorem memset_correct (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (pc : read_pc s = base + memsetOffset)
    (error : read_err s = .None)
    (dstBound : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64) :
    let t := run (Memset.fuel (r (.GPR 2#5) s).toNat) s
    Returned s t ∧
      (∀ a, t.mem a = Memset.image s.mem (r (.GPR 0#5) s)
        ((r (.GPR 1#5) s).setWidth 8) (r (.GPR 2#5) s).toNat a) ∧
      MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s t := by
  arm_word_nf at dstBound ⊢
  have correct := Memset.program_correct s (base + memsetOffset) code.memset pc error dstBound
  arm_word_nf at correct
  rcases correct with ⟨err, ret, _, prog, regs, memory⟩
  refine ⟨⟨ret, err, prog, ?_, ?_, ?_⟩, memory, ?_⟩
  · exact regs (.GPR 31#5) (by simp [Memset.Preserved])
  · intro reg lo hi
    apply regs
    simp only [Memset.Preserved]
    constructor <;> bv_omega
  · intro reg lo hi
    rw [regs (.SFP reg) (by simp only [Memset.Preserved]; bv_omega)]
  · intro address outside
    rw [memory, Memset.image, if_neg (by
      have apart := outside ((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat) (by simp)
      omega)]

/-- Transport an arbitrary architectural read through the real memcpy image. -/
theorem read_copy {s t : ArmState} (dst src : BitVec 64) (count offset bytes : Nat)
    (memory : ∀ a, t.mem a = Memcpy.image s.mem dst src count a)
    (dstBound : dst.toNat + count ≤ 2^64) (srcBound : src.toNat + count ≤ 2^64)
    (inside : offset + bytes ≤ count) :
    read_mem_bytes bytes (dst + BitVec.ofNat 64 offset) t =
      read_mem_bytes bytes (src + BitVec.ofNat 64 offset) s := by
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.State.read_mem_bytes_eq_mem_read_bytes]
  apply BitVec.eq_of_extractLsByte_eq
  intro i
  by_cases hi : i < bytes
  · have dstReadBound : (dst + BitVec.ofNat 64 offset).toNat + bytes ≤ 2^64 := by
      bv_omega
    have srcReadBound : (src + BitVec.ofNat 64 offset).toNat + bytes ≤ 2^64 := by
      bv_omega
    rw [Memory.extractLsByte_read_bytes dstReadBound,
      Memory.extractLsByte_read_bytes srcReadBound, if_pos hi, if_pos hi]
    change t.mem _ = s.mem _
    rw [memory, Memcpy.image, if_pos (by bv_omega)]
    congr 1
    bv_omega
  · rw [BitVec.extractLsByte_ge (by omega), BitVec.extractLsByte_ge (by omega)]

/-- The combine wrapper copies every one of the 112 state bytes. -/
theorem StateAt.of_copy {s t : ArmState} {dst src : BitVec 64} {value : StreamState}
    (source : StateAt s src value)
    (memory : ∀ a, t.mem a = Memcpy.image s.mem dst src 112 a)
    (dstBound : dst.toNat + 112 ≤ 2^64) (srcBound : src.toNat + 112 ≤ 2^64) :
    StateAt t dst value := by
  constructor
  · intro i
    have bound : i.val < 64 := by simpa only [vectorByteArray_size] using i.isLt
    have addressNat : (dst + BitVec.ofNat 64 i.val).toNat = dst.toNat + i.val := by
      bv_omega
    rw [memory, Memcpy.image, if_pos (by rw [addressNat]; omega),
      addressNat, Nat.add_sub_cancel_left]
    exact source.buffer i
  · intro i
    have bound := i.isLt
    have destEq : dst + 64#64 + BitVec.ofNat 64 (4 * i.val) =
        dst + BitVec.ofNat 64 (64 + 4 * i.val) := by bv_omega
    have sourceEq : src + 64#64 + BitVec.ofNat 64 (4 * i.val) =
        src + BitVec.ofNat 64 (64 + 4 * i.val) := by bv_omega
    rw [destEq, read_copy dst src 112 (64 + 4 * i.val) 4 memory dstBound srcBound (by omega),
      ← sourceEq]
    exact source.chaining i
  · rw [read_copy dst src 112 96 8 memory dstBound srcBound (by decide)]
    exact source.buffered
  · rw [read_copy dst src 112 104 8 memory dstBound srcBound (by decide)]
    exact source.byteLen

end SszArm.Hash
