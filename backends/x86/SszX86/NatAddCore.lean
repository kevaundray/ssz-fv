import SszX86.NatAddImpl
import SszX86.DelimitedCore
import SszX86.NatCompareTrim
import SszNatAdd
import SszNatArithmeticMemory

namespace SszX86.NatAdd
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

macro "natadd_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatAdd.step_at _ _ $hc
     (SszX86.NatAdd.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatAdd.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatAdd.program, SszX86.NatAdd.directives,
      SszX86.NatAdd.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "natadd_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

abbrev OutputMapped (s : MachineData) : Prop :=
  UintCodec.Large.Mapped s.dmem s.regs.rdi.toBitVec 68

macro "natadd_output " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $byteCount))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 68)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (natadd_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))

/-- The input view records the original list, including any redundant zeros. -/
theorem operand_view (m : DataMem) (operand : SszNative.NatOperand)
    (stored : operand.At (widthLoad m)) :
    NatCompare.View m operand.pointer operand.payload operand.words := by
  cases operand with
  | small limb => exact Or.inl ⟨rfl, rfl⟩
  | large pointer words =>
    change NatCompare.View m pointer (BitVec.ofNat 64 words.length) words
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine Or.inr ⟨?_, rfl, by omega, ?_⟩
    · intro zero
      simp [zero] at positive
    · intro i
      simpa only [width_address] using widthLoad_eq m _ _ _ (limbs i)

end SszX86.NatAdd
