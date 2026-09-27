import SszX86.ByteViewMemory

namespace SszX86.ByteView
open UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem store_cps (s : MachineData) (address : BitVec 64) {w : Width}
    (value : w.type) (ret : MachineData → Effects) (post : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem address w.bytes = some old)
    (next : (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All post) :
    (MachineData.store s address value ret).All post := by
  obtain ⟨old, hl⟩ := hmap
  simpa only [MachineData.store, Effects.All, hl] using next

private theorem mapped_load_zero (m : DataMem) (out : BitVec 64) (hm : Mapped m out)
    (byteCount : Nat) (hb : byteCount ≤ 80) :
    ∃ value, Mem.loadInt m out byteCount = some value := by
  simpa using mapped_load m out hm 0 byteCount (by simpa using hb)

macro "view_store " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply mapped_load_zero (byteCount := $byteCount))
  else
    `(tactic| apply mapped_load (offset := $offset) («width» := $byteCount))
  `(tactic|
    (view_vector_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply store_cps
     · $loadTac
       · repeat' first | exact $hm | apply mapped_store
       · decide
     simp only [Effects.All]))

theorem success_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (successReady s, base + 7720)) :
    Eventually (step e) P (s, base + 2759) := by
  view_store 149 at 16 width 1 using hc mapped hm
  view_store 150 at 24 width 8 using hc mapped hm
  view_store 151 at 32 width 8 using hc mapped hm
  view_vector_step 152 using hc
  uint_tail_store 162 at 0 width 8 using (uint_codeAt e base hc) mapped hm
  uint_width_step 163 using (uint_codeAt e base hc)
  simpa [successReady, successMem] using hp

theorem limit_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (limitReady s, base + 7720)) :
    Eventually (step e) P (s, base + 2591) := by
  view_store 118 at 64 width 8 using hc mapped hm
  view_store 119 at 56 width 8 using hc mapped hm
  view_store 120 at 8 width 8 using hc mapped hm
  view_store 121 at 16 width 8 using hc mapped hm
  view_store 122 at 24 width 8 using hc mapped hm
  view_store 123 at 32 width 8 using hc mapped hm
  view_store 124 at 40 width 8 using hc mapped hm
  view_store 125 at 48 width 8 using hc mapped hm
  view_store 126 at 72 width 4 using hc mapped hm
  view_vector_step 127 using hc
  uint_tail_store 217 at 0 width 8 using (uint_codeAt e base hc) mapped hm
  simpa [limitReady, limitMem] using hp

theorem success_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Tail.Separated s)
    (P : MachineState → Prop)
    (hp : P (returned (successReady s) saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 2759) := by
  apply success_stores e base hc s hm P
  apply BoolCodec.epilogue e base (UintCodec.bool_codeAt e base (uint_codeAt e base hc))
    (successReady s) saved
  · exact Tail.frame_saved s (successReady s) saved hs
      (frame_tail (success_frame s hs.outputHigh)) ha
  · exact hp

theorem limit_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Tail.Separated s)
    (P : MachineState → Prop)
    (hp : P (returned (limitReady s) saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 2591) := by
  apply limit_stores e base hc s hm P
  apply BoolCodec.epilogue e base (UintCodec.bool_codeAt e base (uint_codeAt e base hc))
    (limitReady s) saved
  · exact Tail.frame_saved s (limitReady s) saved hs
      (frame_tail (limit_frame s hs.outputHigh)) ha
  · exact hp

end SszX86.ByteView
