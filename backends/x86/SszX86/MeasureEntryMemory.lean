import SszX86.MeasureOwned
import SszX86.MeasureSetup
import SszX86.MeasureFrame

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

theorem saved_span (s : MachineData) (a : BitVec 64)
    (inside : InSpan a (s.regs.rsp.toBitVec - 48) 48) :
    InSpan a (s.regs.rsp.toBitVec - 280) 280 := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨232 + i, by omega, ?_⟩
  bv_omega

theorem saved_frame (s : MachineData) :
    MemoryFrame s.dmem (savedMem s) (fun a => InSpan a (s.regs.rsp.toBitVec - 280) 280) := by
  intro a outside
  apply Dispatch.saved_lookup s a
  intro i hi equal
  exact outside (saved_span s a ⟨i, hi, equal⟩)

theorem Owned.saved_descriptor {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    DescAt (savedMem s) s.regs.rsi.toBitVec desc := by
  apply descriptor_frame s.dmem (savedMem s) _ (saved_frame s) _ desc _ owned.descriptor
  intro a borrowed inside
  apply owned.readonly a _ (Or.inr (Or.inr (Or.inr inside)))
  rcases borrowed with live | limbs
  · exact Or.inl live
  · exact Or.inr (Or.inr (Or.inl limbs))

theorem Owned.saved_value {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    ValueAt (savedMem s) s.regs.rdx.toBitVec buffer value := by
  apply value_frame s.dmem (savedMem s) _ (saved_frame s) _ buffer value _ owned.valueStored
  intro a borrowed inside
  apply owned.readonly a _ (Or.inr (Or.inr (Or.inr inside)))
  rcases borrowed with live | bytes
  · exact Or.inr (Or.inl live)
  · exact Or.inr (Or.inr (Or.inr bytes))

theorem Owned.saved_header {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    ArenaAt (savedMem s) s.regs.rcx.toBitVec address capacity used := by
  have fields (off : Nat) (bound : off + 8 ≤ 24) :
      widthLoad (savedMem s) (s.regs.rcx.toNat + off) 8 =
        widthLoad s.dmem (s.regs.rcx.toNat + off) 8 := by
    unfold widthLoad
    rw [← UInt64.toNat_toBitVec, width_address]
    congr 1
    apply frame_load s.dmem (savedMem s) _ (saved_frame s)
    intro i hi inside
    obtain ⟨j, hj, equal⟩ := inside
    apply owned.headerStack (off + i) (by omega) j (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact equal
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, UInt64.toNat_toBitVec] using
      (fields 0 (by decide)).trans owned.arena.1
  · exact (fields 8 (by decide)).trans owned.arena.2.1
  · exact (fields 16 (by decide)).trans owned.arena.2.2

theorem Owned.saved_table {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    TableAt (savedMem s) base := by
  intro i hi
  rw [saved_frame s _ (by
    intro inside
    apply owned.tableReadonly _ ⟨i, by simpa only [tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩
    exact Or.inr (Or.inr (Or.inr inside)))]
  exact owned.table i hi

theorem Owned.saved_stack_mapped {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
  have hm := Delimited.Reservation.mapped_subrange s.dmem (s.regs.rsp.toBitVec - 280)
    280 232 48 owned.stackMapped (by decide)
  have pointer : s.regs.rsp.toBitVec - 280 + BitVec.ofNat 64 232 = s.regs.rsp.toBitVec - 48 := by
    bv_omega
  rwa [pointer] at hm

end SszX86.Measure
