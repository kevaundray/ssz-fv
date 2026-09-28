import SszX86.MeasureBitsResources
import SszX86.NatFromU128MemoryFacts

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem frame_mono (before after : DataMem) (small large : BitVec 64 → Prop)
    (frame : MemoryFrame before after small) (included : ∀ a, small a → large a) :
    MemoryFrame before after large := by
  intro a outside
  exact frame a (fun inside => outside (included a inside))

theorem frame_trans (before middle after : DataMem) (left right : BitVec 64 → Prop)
    (first : MemoryFrame before middle left) (second : MemoryFrame middle after right) :
    MemoryFrame before after (fun a => left a ∨ right a) := by
  intro a outside
  exact (second a (fun written => outside (Or.inr written))).trans
    (first a (fun written => outside (Or.inl written)))

theorem store_frame (m : DataMem) (pointer : BitVec 64) (byteCount : Nat) (value : Int) :
    MemoryFrame m (Mem.storeInt m pointer byteCount value) (fun a => InSpan a pointer byteCount) := by
  intro a outside
  apply memmove_store_lookup_outside
  intro i hi equal
  exact outside ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩

/-- Geometry comes from the original free suffix and actual reserve guards,
including all invalid-arena failure cases; it is not a future allocation premise. -/
theorem reserve_geometry (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
    address.toNat + used.toNat ≤ r.pointer ∧
    r.pointer + 16 = address.toNat + r.used ∧
    r.used ≤ capacity.toNat ∧ r.pointer + 16 ≤ 2^64 ∧ r.used < 2^64 := by
  obtain ⟨checks, rfl⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  dsimp only
  have cursor := Arena.used_le_start address.toNat used.toNat
  have fits : Arena.start address.toNat used.toNat + 16 ≤ capacity.toNat := checks.2.2.2.2.2
  have positive := owned.arenaNonzero (by omega)
  have bound := owned.arenaBound
  refine ⟨by omega, ?_, by omega, ?_, fits, ?_, checks.2.2.2.2.1⟩
  · rw [Arena.start_pointer]
    exact Arena.aligned_mod _
  · simp only [Arena.finish, Nat.add_assoc]
  · omega

theorem reserve_mapped (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    Large.Mapped s.dmem (BitVec.ofNat 64 r.pointer) 16 := by
  have geometry := reserve_geometry s desc value buffer address capacity used owned r reserved
  have mapping := Delimited.Reservation.mapped_subrange s.dmem (address + used)
    (capacity.toNat-used.toNat) (r.pointer-(address.toNat+used.toNat)) 16 owned.freeMapped
    (by omega)
  have pointer : address + used + BitVec.ofNat 64 (r.pointer-(address.toNat+used.toNat)) =
      BitVec.ofNat 64 r.pointer := by bv_omega
  rw [pointer] at mapping
  exact mapping

theorem allocation_in_free (address used capacity : BitVec 64) (pointer byteCount : Nat)
    (start : address.toNat + used.toNat ≤ pointer)
    (finish : pointer + byteCount ≤ address.toNat + capacity.toNat)
    (a : BitVec 64) (inside : InSpan a (BitVec.ofNat 64 pointer) byteCount) :
    InSpan a (address + used) (capacity.toNat - used.toNat) := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨pointer - (address.toNat + used.toNat) + i, by omega, ?_⟩
  bv_omega

/-- Original active observations survive any already-proved prefix confined to
its owned result, committed cursor, original free suffix, and actual local frame. -/
theorem original_inputs (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used) (m : DataMem)
    (frame : MemoryFrame s.dmem m (fun a =>
      InSpan a s.regs.rbx.toBitVec 72 ∨ InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨
      InSpan a (address + used) (capacity.toNat - used.toNat) ∨
      InSpan a (s.regs.rsp.toBitVec - 16) 232)) :
    DescAt m s.regs.rsi.toBitVec desc ∧ ValueAt m s.regs.r14.toBitVec buffer value := by
  constructor
  · apply descriptor_frame s.dmem m _ frame _ desc _ owned.descriptor
    intro a borrowed
    apply owned.readonly a
    rcases borrowed with live | limbs
    · exact Or.inl live
    · exact Or.inr (Or.inr (Or.inl limbs))
  · apply value_frame s.dmem m _ frame _ buffer value _ owned.valueStored
    intro a borrowed
    apply owned.readonly a
    rcases borrowed with live | limbs
    · exact Or.inr (Or.inl live)
    · exact Or.inr (Or.inr (Or.inr limbs))

end SszX86.Measure.Bits
