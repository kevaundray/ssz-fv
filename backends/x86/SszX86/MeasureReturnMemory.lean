import SszX86.MeasureReturn
import SszX86.MeasureSetup
import SszX86.MeasureArenaFrame

namespace SszX86.Measure
open SszNative SszNative.Serialize BoolCodec UintCodec

abbrev saved := Dispatch.saved

/-- All seven words are derived from the actual six PUSH stores and original
return slot; they are not asserted at the future body exit. -/
theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 264) (saved s ra) := by
  have stored := Dispatch.saved_at s ra ret
  have offsets (off : BitVec 64) : s.regs.rsp.toBitVec - 264 + off =
      s.regs.rsp.toBitVec - 360 + (off + 96) := by bv_omega
  simpa only [SavedAt, BoolCodec.SavedAt, offsets, BitVec.reduceAdd] using stored

theorem savedAt_frame (before after : DataMem) (sp : BitVec 64) (registers : Saved)
    (writable : BitVec 64 → Prop) (frame : MemoryFrame before after writable)
    (untouched : ∀ i < 56, ¬ writable (sp + 216 + BitVec.ofNat 64 i))
    (stored : SavedAt before sp registers) : SavedAt after sp registers := by
  have unchangedLoad (off : Nat) (bound : off + 8 ≤ 56) :
      Mem.loadInt after (sp + 216 + BitVec.ofNat 64 off) 8 =
        Mem.loadInt before (sp + 216 + BitVec.ofNat 64 off) 8 := by
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

theorem BodyPost.saved {s t : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (post : BodyPost s desc value buffer address capacity used t)
    (owned : BodyOwned s desc value buffer address capacity used)
    (registers : Saved) (stored : SavedAt s.dmem s.regs.rsp.toBitVec registers) :
    SavedAt t.dmem t.regs.rsp.toBitVec registers := by
  rw [post.stack]
  exact savedAt_frame s.dmem t.dmem s.regs.rsp.toBitVec registers _ post.frame
    owned.saved_untouched stored

end SszX86.Measure
