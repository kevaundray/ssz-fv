import SszArm.DispatchScalarOwned

namespace SszArm.Dispatch.Unsigned

open UintCodec (widthLoad)

def arenaBase (s : ArmState) := read_mem_bytes 8 (r (.GPR 4#5) s) s
def arenaCapacity (s : ArmState) := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
def arenaUsed (s : ArmState) := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s

/-- Physical available-suffix separation, stated at the original X4/SP ABI. -/
structure Storage (s : ArmState) (data : Ssz.Bytes) : Prop where
  valid : SszNative.Arena.Valid (arenaBase s).toNat (arenaCapacity s).toNat (arenaUsed s).toNat
  source : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨ data.size = 0 ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 2#5) s).toNat ∨
    (r (.GPR 2#5) s).toNat + data.size ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  output : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 80 ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  stack : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 31#5) s).toNat - 384 ∨
    (r (.GPR 31#5) s).toNat ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  header : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 4#5) s).toNat ∨
    (r (.GPR 4#5) s).toNat + 24 ≤ (arenaBase s).toNat + (arenaUsed s).toNat

structure Owned (s : ArmState) (width : Nat) (data : Ssz.Bytes) : Prop where
  scalar : Scalar.Owned s .uint width data
  inputPhysical : data.size < 2^63
  widthScratch : Scalar.pointer s ≠ 0#64 →
    (Scalar.pointer s).toNat + 8 * (Scalar.payload s).toNat ≤ (r (.GPR 31#5) s).toNat - 384 ∨
      (r (.GPR 31#5) s).toNat ≤ (Scalar.pointer s).toNat
  headerBound : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  headerStack : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 384 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 4#5) s).toNat
  headerSource : data.size = 0 ∨
    (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 2#5) s).toNat ∨
    (r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 4#5) s).toNat
  headerOutput : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 4#5) s).toNat
  storage : ((arenaCapacity s).toNat = 0 ∧ (arenaUsed s).toNat = 0) ∨ Storage s data
  descriptorHeader : (r (.GPR 1#5) s).toNat + 24 ≤ (r (.GPR 4#5) s).toNat + 16 ∨
    (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 1#5) s).toNat
  descriptorStorage : (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (r (.GPR 1#5) s).toNat ∨
    (r (.GPR 1#5) s).toNat + 24 ≤ (arenaBase s).toNat + (arenaUsed s).toNat
  limbsHeader : Scalar.pointer s ≠ 0#64 → Scalar.payload s ≠ 0#64 →
    (Scalar.pointer s).toNat + 8 * (Scalar.payload s).toNat ≤ (r (.GPR 4#5) s).toNat + 16 ∨
      (r (.GPR 4#5) s).toNat + 24 ≤ (Scalar.pointer s).toNat
  limbsStorage : Scalar.pointer s ≠ 0#64 → Scalar.payload s ≠ 0#64 →
    (arenaUsed s).toNat = (arenaCapacity s).toNat ∨
    (arenaBase s).toNat + (arenaCapacity s).toNat ≤ (Scalar.pointer s).toNat ∨
      (Scalar.pointer s).toNat + 8 * (Scalar.payload s).toNat ≤ (arenaBase s).toNat + (arenaUsed s).toNat

theorem Owned.header {s : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (offset : Nat) (within : offset ≤ 16) :
    read_mem_bytes 8 (r (.GPR 19#5) (entered s .uint) + BitVec.ofNat 64 offset) (entered s .uint) =
      read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) s := by
  rw [entered_arena]
  apply entered_read s .uint owned.scalar.entry.stackLow
  · have bound := owned.headerBound
    bv_omega
  · have bound := owned.headerBound
    have separate := owned.headerStack
    bv_omega

theorem Owned.arena {s : ArmState} {width : Nat} {data : Ssz.Bytes} (owned : Owned s width data) :
    UintCodec.arenaBase (entered s .uint) = arenaBase s ∧
    UintCodec.arenaCapacity (entered s .uint) = arenaCapacity s ∧
    UintCodec.arenaUsed (entered s .uint) = arenaUsed s := by
  constructor
  · simpa [UintCodec.arenaBase, arenaBase] using owned.header 0 (by decide)
  constructor
  · simpa [UintCodec.arenaCapacity, arenaCapacity] using owned.header 8 (by decide)
  · simpa [UintCodec.arenaUsed, arenaUsed] using owned.header 16 (by decide)

theorem Owned.body {s : ArmState} {width : Nat} {data : Ssz.Bytes} (owned : Owned s width data) :
    UintCodec.Allocated.Owned (entered s .uint) data := by
  obtain ⟨base, capacity, used⟩ := owned.arena
  refine ⟨owned.scalar.uint_separated, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using owned.headerBound
  · have low := owned.scalar.stackLow
    have separate := owned.headerStack
    simp only [BitVec.ofNat_eq_ofNat, entered_arena, entered_sp, bodySP]
    bv_omega
  · simpa using owned.headerSource
  · simpa using owned.headerOutput
  · rcases owned.storage with empty | storage
    · exact Or.inl (by simpa only [capacity, used] using empty)
    · apply Or.inr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [base, capacity, used] using storage.valid
      · simpa [base, capacity, used] using storage.source
      · simpa [base, capacity, used] using storage.output
      · have low := owned.scalar.stackLow
        have separate := storage.stack
        simp only [BitVec.ofNat_eq_ofNat, base, capacity, used, entered_sp, bodySP]
        bv_omega
      · simpa [base, capacity, used] using storage.header

theorem Owned.width {s : ArmState} {width : Nat} {data : Ssz.Bytes} (owned : Owned s width data) :
    UintCodec.WidthPair (entered s .uint) width := by
  unfold UintCodec.WidthPair
  rw [owned.scalar.header 8 (by decide), owned.scalar.header 16 (by decide)]
  exact owned.scalar.uint_pair

theorem Owned.scratch {s : ArmState} {width : Nat} {data : Ssz.Bytes} (owned : Owned s width data) :
    UintCodec.WidthScratchSeparated (entered s .uint) := by
  have low := owned.scalar.stackLow
  unfold UintCodec.WidthScratchSeparated
  rw [owned.scalar.header 8 (by decide), owned.scalar.header 16 (by decide)]
  simp only [entered_sp, bodySP]
  constructor
  · bv_omega
  · intro nonzero
    have separate := owned.widthScratch nonzero
    simp only [Scalar.pointer, Scalar.payload] at separate
    bv_omega

theorem Owned.input {s : ArmState} {width : Nat} {data : Ssz.Bytes} (owned : Owned s width data) :
    UintCodec.Small.Input (entered s .uint) data := by
  refine ⟨?_, owned.inputPhysical, ?_, ?_, ?_, ?_⟩
  · change r (.GPR 3#5) (entered s .uint) = BitVec.ofNat 64 data.size
    rw [entered_reg s .uint 3#5 (by decide) (by decide) (by decide), ← owned.scalar.length]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simpa using owned.scalar.inputBound
  · have low := owned.scalar.stackLow
    simp only [BitVec.ofNat_eq_ofNat, entered_sp, bodySP]
    bv_omega
  · have low := owned.scalar.stackLow
    have separate := owned.scalar.inputStack
    simp only [BitVec.ofNat_eq_ofNat, entered_reg _ _ 2#5 (by decide) (by decide) (by decide), entered_sp, bodySP]
    bv_omega
  · intro i within
    have bytes := owned.scalar.entered_input i within
    apply BitVec.eq_of_toNat_eq
    simpa [UintCodec.widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat,
      entered_reg, Array.getElem?_eq_getElem within] using Option.some.inj bytes

end SszArm.Dispatch.Unsigned
