import SszX86.BoolExec

namespace SszX86.BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 200000

private theorem store_cps (s : MachineData) (address : BitVec 64) {w : Width}
    (value : w.type) (ret : MachineData → Effects) (post : MachineState → Prop)
    (mapped : ∃ old, Mem.loadInt s.dmem address w.bytes = some old)
    (next : (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All post) :
    (MachineData.store s address value ret).All post := by
  obtain ⟨old, hl⟩ := mapped
  simpa only [MachineData.store, Effects.All, hl] using next

private theorem mapped_load_zero (m : DataMem) (out : BitVec 64) (hm : Mapped m out)
    (width : Nat) (hb : width ≤ 80) :
    ∃ value, Mem.loadInt m out width = some value := by
  simpa using mapped_load m out hm 0 width (by simpa using hb)

macro "bool_store " row:num " at " offset:num " width " width:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply mapped_load_zero (width := $width))
  else
    `(tactic| apply mapped_load (offset := $offset) (width := $width))
  `(tactic|
    (bool_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply store_cps
     · $loadTac
       · repeat' first | exact $hm | apply mapped_store
       · decide
     simp only [Effects.All]))

/-- All scope-error stores and real jumps, ending at the actual epilogue. -/
theorem scope_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec) (P : MachineState → Prop)
    (hp : Eventually (step e) P
      ({s with dmem := scopeMem s.dmem s.regs.rdi.toBitVec s.regs.r14.toBitVec}, base + 7720)) :
    Eventually (step e) P (s, base + 1580) := by
  bool_store 9 at 64 width 8 using hc mapped hm
  bool_store 10 at 56 width 8 using hc mapped hm
  bool_store 11 at 24 width 8 using hc mapped hm
  bool_store 12 at 32 width 8 using hc mapped hm
  bool_step 13 using hc
  bool_store 26 at 8 width 8 using hc mapped hm
  bool_store 27 at 16 width 8 using hc mapped hm
  bool_store 28 at 40 width 8 using hc mapped hm
  bool_store 29 at 48 width 8 using hc mapped hm
  bool_store 30 at 72 width 4 using hc mapped hm
  bool_step 31 using hc
  bool_store 34 at 0 width 8 using hc mapped hm
  simpa [scopeMem] using hp

/-- All invalid-byte stores and real jumps; the byte has already been loaded. -/
theorem bad_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec) (P : MachineState → Prop)
    (hp : Eventually (step e) P
      ({s with dmem := badMem s.dmem s.regs.rdi.toBitVec s.regs.rax.toBitVec}, base + 7720)) :
    Eventually (step e) P (s, base + 2674) := by
  bool_store 16 at 64 width 8 using hc mapped hm
  bool_store 17 at 56 width 8 using hc mapped hm
  bool_store 18 at 48 width 8 using hc mapped hm
  bool_store 19 at 40 width 8 using hc mapped hm
  bool_store 20 at 8 width 8 using hc mapped hm
  bool_store 21 at 16 width 8 using hc mapped hm
  bool_store 22 at 24 width 8 using hc mapped hm
  bool_store 23 at 32 width 8 using hc mapped hm
  bool_store 24 at 72 width 4 using hc mapped hm
  bool_step 25 using hc
  bool_store 34 at 0 width 8 using hc mapped hm
  simpa [badMem] using hp

/-- Both successful payload stores and the common success tag, through jumps. -/
theorem success_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec) (value : Bool)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec value}, base + 7720)) :
    Eventually (step e) P (s, if value then base + 75 else base + 2663) := by
  cases value
  · bool_store 14 at 16 width 2 using hc mapped hm
    bool_step 15 using hc
    bool_store 32 at 0 width 8 using hc mapped hm
    bool_step 33 using hc
    simpa [successMem] using hp
  · bool_store 7 at 16 width 2 using hc mapped hm
    bool_step 8 using hc
    bool_store 32 at 0 width 8 using hc mapped hm
    bool_step 33 using hc
    simpa [successMem] using hp

end SszX86.BoolCodec
