import SszX86.MeasureBitsMemory
import SszX86.MeasureBitsOutputMemory

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

def vectorCommitMem (s : MachineData) (r : Arena.Reservation) (wide : BitVec 128) : DataMem :=
  NatFromU128.commitMem s.dmem s.regs.rcx.toBitVec (BitVec.ofNat 64 r.pointer)
    (BitVec.ofNat 64 r.used) (wide.setWidth 64) ((wide >>> 64).setWidth 64)

theorem vector_commit_frame (s : MachineData) (r : Arena.Reservation) (wide : BitVec 128) :
    MemoryFrame s.dmem (vectorCommitMem s r wide) (fun a =>
      InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨ InSpan a (BitVec.ofNat 64 r.pointer) 16) := by
  intro a outside
  apply NatFromU128.commit_frame
  · intro i hi equal
    exact outside (Or.inl ⟨i, hi, equal⟩)
  · intro i hi equal
    exact outside (Or.inr ⟨i, hi, equal⟩)

theorem vector_commit_inputs (s : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    DescAt (vectorCommitMem s r bits.count) s.regs.rsi.toBitVec (.bitVector expected) ∧
    ValueAt (vectorCommitMem s r bits.count) s.regs.r14.toBitVec buffer (.bits bits) := by
  have geometry := reserve_geometry s _ _ buffer address capacity used owned r reserved
  apply original_inputs s _ _ buffer address capacity used owned
  apply frame_mono _ _ _ _ (vector_commit_frame s r bits.count)
  intro a written
  rcases written with cursor | payload
  · exact Or.inr (Or.inl cursor)
  · exact Or.inr (Or.inr (Or.inl
      (allocation_in_free address used capacity r.pointer 16 geometry.2.2.1
        (by omega) a payload)))

theorem vector_commit_operand (s : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    (NatOperand.large (BitVec.ofNat 64 r.pointer)
      [bits.count.setWidth 64, (bits.count >>> 64).setWidth 64]).At
      (widthLoad (vectorCommitMem s r bits.count)) := by
  have geometry := reserve_geometry s _ _ buffer address capacity used owned r reserved
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer :=
    Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pointerNat] using geometry.1
  · simpa only [pointerNat] using geometry.2.1
  · simpa only [pointerNat, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
      using geometry.2.2.2.2.2.1
  · exact NatFromU128.commit_words s.dmem s.regs.rcx.toBitVec
      (BitVec.ofNat 64 r.pointer) (BitVec.ofNat 64 r.used)
      (bits.count.setWidth 64) ((bits.count >>> 64).setWidth 64)
      (by rw [pointerNat]; exact geometry.2.2.2.2.2.1)

theorem vector_commit_arena (s : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    widthLoad (vectorCommitMem s r bits.count) s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad (vectorCommitMem s r bits.count) (s.regs.rcx.toNat + 8) 8 = some capacity.toNat ∧
    widthLoad (vectorCommitMem s r bits.count) (s.regs.rcx.toNat + 16) 8 = some r.used := by
  have geometry := reserve_geometry s _ _ buffer address capacity used owned r reserved
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
  have allocatedHeader : Body.Apart r.pointer 16 s.regs.rcx.toNat 24 := by
    have separated := owned.freeHeader
    unfold Body.Apart at separated ⊢
    omega
  have keep (off : Nat) (within : off + 8 ≤ 16) :
      widthLoad (vectorCommitMem s r bits.count) (s.regs.rcx.toNat + off) 8 =
        widthLoad s.dmem (s.regs.rcx.toNat + off) 8 := by
    apply NatFromU128.commit_width_preserved
    · have bound := owned.headerBound; omega
    · exact owned.headerBound
    · rw [pointerNat]; exact geometry.2.2.2.2.2.1
    · simp only [Body.Apart, UInt64.toNat_toBitVec]
      omega
    · rw [pointerNat]
      unfold Body.Apart at allocatedHeader ⊢
      omega
  refine ⟨?_, (keep 8 (by decide)).trans owned.arena.2.1, ?_⟩
  · simpa only [Nat.add_zero] using (keep 0 (by decide)).trans owned.arena.1
  · have cursor := NatFromU128.commit_cursor s.dmem s.regs.rcx.toBitVec
      (BitVec.ofNat 64 r.pointer) (BitVec.ofNat 64 r.used)
      (bits.count.setWidth 64) ((bits.count >>> 64).setWidth 64)
      owned.headerBound (by rw [pointerNat]; exact geometry.2.2.2.2.2.1)
      (by rw [pointerNat]; exact allocatedHeader.symm)
    simpa only [vectorCommitMem, UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt geometry.2.2.2.2.2.2] using cursor

end SszX86.Measure.Bits
