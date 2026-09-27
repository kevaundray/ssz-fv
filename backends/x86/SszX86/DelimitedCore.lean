import SszX86.DelimitedImpl
import SszX86.UintBodyMemory
import SszBitView

namespace SszX86.Delimited
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "delimited_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.Delimited.step_at _ _ $hc
     (SszX86.Delimited.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.Delimited.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Delimited.program, SszX86.Delimited.directives,
      SszX86.Delimited.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

theorem word_cast (v : BitVec 64) : BitVec.ofInt 64 (v.toNat : Int) = v := by bv_omega

theorem byte_cast (v : BitVec 8) : BitVec.ofInt 8 (v.toNat : Int) = v := by bv_omega

macro "delimited_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), word_cast, byte_cast])

theorem store_cps (s : MachineData) (address : BitVec 64) {w : Width}
    (value : w.type) (ret : MachineData → Effects) (post : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem address w.bytes = some old)
    (next : (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All post) :
    (MachineData.store s address value ret).All post := by
  obtain ⟨old, hl⟩ := hmap
  simpa only [MachineData.store, Effects.All, hl] using next

/-- No extra output padding is required by this callee. -/
abbrev OutputMapped (s : MachineData) : Prop :=
  UintCodec.Large.Mapped s.dmem s.regs.rdi.toBitVec 76

theorem mapped_load_zero (m : DataMem) (p : BitVec 64) (capacity byteCount : Nat)
    (hm : UintCodec.Large.Mapped m p capacity) (hw : byteCount ≤ capacity) :
    ∃ old, Mem.loadInt m p byteCount = some old := by
  simpa using UintCodec.Large.mapped_load m p capacity 0 byteCount hm (by simpa using hw)

macro "delimited_output " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply mapped_load_zero (capacity := 76) (byteCount := $byteCount))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 76)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (delimited_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))



end SszX86.Delimited
