import SszX86.EmitOwned

namespace SszX86.Emit
open SszNative UintCodec

theorem span_shift (p : BitVec 64) (byteOffset byteCount total : Nat)
    (bound : byteOffset + byteCount ≤ total) {a : BitVec 64}
    (inside : InSpan a (p + BitVec.ofNat 64 byteOffset) byteCount) : InSpan a p total := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨byteOffset + i, by omega, ?_⟩
  rw [memmove_addr_add]

theorem natAt_frame (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (p : BitVec 64) (operand : NatOperand)
    (header : ∀ a, InSpan a p 16 → ¬ writable a)
    (limbs : ∀ a, NatBorrowed operand a → ¬ writable a)
    (stored : NatAt before p operand) : NatAt after p operand := by
  have headerLoad (off : Nat) (bound : off + 8 ≤ 16) :
      widthLoad after (p.toNat + off) 8 = widthLoad before (p.toNat + off) 8 := by
    unfold widthLoad
    rw [width_address]
    congr 1
    apply frame_load before after writable frame
    intro i hi
    exact header _ (span_shift p off 8 16 bound ⟨i, hi, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using (headerLoad 0 (by decide)).trans stored.1
  · exact (headerLoad 8 (by decide)).trans stored.2.1
  · cases operand with
    | small limb => trivial
    | large pointer words =>
      obtain ⟨positive, aligned, bound, observations⟩ := stored.2.2
      refine ⟨positive, aligned, bound, ?_⟩
      intro i
      have same : widthLoad after (pointer.toNat + 8 * i.val) 8 =
          widthLoad before (pointer.toNat + 8 * i.val) 8 := by
        unfold widthLoad
        rw [width_address]
        congr 1
        apply frame_load before after writable frame
        intro j hj
        exact limbs _ (span_shift pointer (8 * i.val) 8 (8 * words.length)
          (by have := i.isLt; omega) ⟨j, hj, rfl⟩)
      rw [same]
      exact observations i

/-- Every PUSH byte belongs to the original activation's actual writable span. -/
theorem saved_frame (s : MachineData) (written : Nat) :
    MemoryFrame s.dmem (savedMem s) (Writable s written) := by
  intro a outside
  apply Dispatch.saved_lookup s a
  intro i hi equal
  apply outside
  right; right; right
  refine ⟨112 + i, by omega, ?_⟩
  rw [equal]
  bv_omega

theorem Owned.saved_load {s : MachineData} {base : Int64} {desc : SszNative.Serialize.Desc}
    {value : SszNative.Serialize.Value} {buffer ra : BitVec 64} {written : Nat}
    (owned : Owned s base desc value buffer ra written) (p : BitVec 64) (n : Nat)
    (borrowed : ∀ a, InSpan a p n → Borrowed s desc value buffer a) :
    Mem.loadInt (savedMem s) p n = Mem.loadInt s.dmem p n := by
  apply frame_load _ _ _ (saved_frame s written)
  intro i hi
  exact owned.readonly _ (borrowed _ ⟨i, hi, rfl⟩)

theorem Owned.saved_bytes {s : MachineData} {base : Int64} {desc : SszNative.Serialize.Desc}
    {value : SszNative.Serialize.Value} {buffer ra : BitVec 64} {written : Nat}
    (owned : Owned s base desc value buffer ra written) (p : BitVec 64) (bytes : Ssz.Bytes)
    (borrowed : ∀ a, InSpan a p bytes.size → Borrowed s desc value buffer a)
    (stored : BytesAt s.dmem p bytes) : BytesAt (savedMem s) p bytes := by
  intro i hi
  rw [saved_frame s written _ (owned.readonly _ (borrowed _ ⟨i, hi, rfl⟩))]
  exact stored i hi

theorem Owned.saved_table {s : MachineData} {base : Int64} {desc : SszNative.Serialize.Desc}
    {value : SszNative.Serialize.Value} {buffer ra : BitVec 64} {written : Nat}
    (owned : Owned s base desc value buffer ra written) : TableAt (savedMem s) base := by
  intro i hi
  rw [saved_frame s written _ (owned.tableReadonly _ ⟨i, by simpa [tableBytes] using hi, rfl⟩)]
  exact owned.table i hi

end SszX86.Emit
