import SszX86.EmitReturn
import SszX86.EmitSetup

namespace SszX86.Emit
open BoolCodec UintCodec

abbrev saved := Dispatch.saved

/-- The saved activation image is derived from the actual six PUSH writes. -/
theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 152) (saved s ra) := by
  have stored := Dispatch.saved_at s ra ret
  have offsets (off : BitVec 64) : s.regs.rsp.toBitVec - 152 + off =
      s.regs.rsp.toBitVec - 360 + (off + 208) := by bv_omega
  simpa only [SavedAt, BoolCodec.SavedAt, offsets, BitVec.reduceAdd] using stored

theorem frame_load (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (p : BitVec 64) (n : Nat)
    (untouched : ∀ i < n, ¬ writable (p + BitVec.ofNat 64 i)) :
    Mem.loadInt after p n = Mem.loadInt before p n := by
  apply memmove_loadInt_congr
  intro i hi
  exact frame _ (untouched i hi)

theorem frame_mapped (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (p : BitVec 64) (n : Nat)
    (untouched : ∀ i < n, ¬ writable (p + BitVec.ofNat 64 i))
    (hmap : Large.Mapped before p n) : Large.Mapped after p n := by
  intro i hi
  rw [frame _ (untouched i hi)]
  exact hmap i hi

theorem savedAt_frame (before after : DataMem) (sp : BitVec 64) (registers : Saved)
    (writable : BitVec 64 → Prop) (frame : MemoryFrame before after writable)
    (untouched : ∀ i < 56, ¬ writable (sp + 104 + BitVec.ofNat 64 i))
    (stored : SavedAt before sp registers) : SavedAt after sp registers := by
  have unchangedLoad (off : Nat) (bound : off + 8 ≤ 56) :
      Mem.loadInt after (sp + 104 + BitVec.ofNat 64 off) 8 =
        Mem.loadInt before (sp + 104 + BitVec.ofNat 64 off) 8 := by
    apply frame_load before after writable frame
    intro i hi
    rw [memmove_addr_add]
    exact untouched (off + i) (by omega)
  have l0 := unchangedLoad 0 (by decide)
  have l8 := unchangedLoad 8 (by decide)
  have l16 := unchangedLoad 16 (by decide)
  have l24 := unchangedLoad 24 (by decide)
  have l32 := unchangedLoad 32 (by decide)
  have l40 := unchangedLoad 40 (by decide)
  have l48 := unchangedLoad 48 (by decide)
  simp only [show BitVec.ofNat 64 0 = (0 : BitVec 64) by decide,
    BitVec.add_assoc, BitVec.reduceAdd] at l0 l8 l16 l24 l32 l40 l48
  unfold SavedAt at *
  rw [l0, l8, l16, l24, l32, l40, l48]
  exact stored

end SszX86.Emit
