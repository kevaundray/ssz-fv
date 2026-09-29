import SszX86.CodecMeasureFixedFieldsSetup
import SszX86.CodecMeasureFixedMemory
import SszX86.BitVectorStackReads

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec

structure FieldsSlotsAt (m : DataMem) (sp pointer extent : BitVec 64) : Prop where
  pointer_load : Mem.loadInt m (sp + 80) 8 = some (pointer.toNat : Int)
  extent_load : Mem.loadInt m (sp + 72) 8 = some (extent.toNat : Int)

theorem fields_pointer_saved (s : MachineData) :
    Mem.loadInt (fieldsPointerSaved s).dmem (s.regs.rsp.toBitVec + 80) 8 =
      some (s.regs.rax.toNat : Int) := by
  exact BitVector.load_store_word _ _ _

theorem fields_extent_saved (s : MachineData) (pointer : BitVec 64)
    (loaded : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80) 8 = some (pointer.toNat : Int)) :
    FieldsSlotsAt (fieldsExtentSaved s).dmem s.regs.rsp.toBitVec pointer s.regs.rax.toBitVec := by
  constructor
  · change Mem.loadInt (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 72) 8 _) _ 8 = _
    rw [load_store_disjoint _ _ _ _ _ _ (by intro i hi j hj; bv_omega)]
    exact loaded
  · exact BitVector.load_store_word _ _ _

theorem FieldsSlotsAt.frame {before after : DataMem} {sp pointer extent : BitVec 64}
    {writes : Codec.Footprint} (slots : FieldsSlotsAt before sp pointer extent)
    (frame : Codec.MemoryFrame before after writes)
    (protected : ∀ a, Codec.InSpan a (sp + 72) 16 → ¬ writes a) :
    FieldsSlotsAt after sp pointer extent := by
  have load (off : Nat) (range : 72 ≤ off ∧ off + 8 ≤ 88) :
      Mem.loadInt after (sp + BitVec.ofNat 64 off) 8 =
        Mem.loadInt before (sp + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply frame
    apply protected
    refine ⟨off - 72 + i, by omega, ?_⟩
    bv_omega
  exact ⟨(load 80 (by omega)).trans slots.pointer_load,
    (load 72 (by omega)).trans slots.extent_load⟩

/-- The live result buffer occupies only bytes 0..72. Recursive activation and
CALL pushes lie below its base. Arena/header writes use the original ownership
separation, not a coarse frame allowing writes throughout the caller stack. -/
def FieldWorkWrites (sp header address used capacity : BitVec 64) (depth : Nat)
    (a : BitVec 64) : Prop :=
  Codec.InSpan a sp 72 ∨ Codec.StackWrites sp depth a ∨
  Codec.InSpan a (header + 16) 8 ∨
  Codec.InSpan a (address + used) (capacity.toNat - used.toNat)

theorem Owned.field_locals_safe {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra sp : BitVec 64} {bytes depth : Nat}
    (owned : Owned s base r desc address capacity used ra bytes)
    (body : sp.toNat + 136 = s.regs.rsp.toNat) (enough : 136 ≤ bytes)
    (depthBound : depth ≤ sp.toNat) :
    ∀ a, Codec.InSpan a (sp + 72) 72 →
      ¬ FieldWorkWrites sp s.regs.rdx.toBitVec address used capacity depth a := by
  intro a local write
  have low := owned.stack.lowEnough
  have top := owned.return_bound
  have position : sp.toNat + 72 ≤ a.toNat ∧ a.toNat < sp.toNat + 144 := by
    rcases local with ⟨i, hi, same⟩
    bv_omega
  rcases write with output | stack | cursor | arena
  · have bounds := span_bounds (p := sp) (n := 72) (by omega) output
    omega
  · have bounds := stack_bounds depthBound stack
    omega
  · have hb := owned.header_bound
    have cursorBounds : s.regs.rdx.toNat + 16 ≤ a.toNat ∧ a.toNat < s.regs.rdx.toNat + 24 := by
      rcases cursor with ⟨i, hi, same⟩
      bv_omega
    have apart := owned.header_stack.nonempty (by decide) (by omega)
    omega
  · have bounds := free_bounds owned.arena_bound owned.used_bound arena
    have apart := owned.arena_stack.nonempty (by omega) (by omega)
    omega

theorem FieldsSlotsAt.work_frame {before after : DataMem} {sp pointer extent : BitVec 64}
    {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes depth : Nat}
    (slots : FieldsSlotsAt before sp pointer extent)
    (owned : Owned s base r desc address capacity used ra bytes)
    (body : sp.toNat + 136 = s.regs.rsp.toNat) (enough : 136 ≤ bytes)
    (depthBound : depth ≤ sp.toNat)
    (frame : Codec.MemoryFrame before after
      (FieldWorkWrites sp s.regs.rdx.toBitVec address used capacity depth)) :
    FieldsSlotsAt after sp pointer extent := by
  apply slots.frame frame
  intro a inside
  apply owned.field_locals_safe body enough depthBound a
  rcases inside with ⟨i, hi, same⟩
  exact ⟨i, by omega, same⟩

end SszX86.CodecMeasureFixed
