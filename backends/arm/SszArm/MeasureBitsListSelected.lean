import SszArm.MeasureBitsListPrefixStep
import SszArm.MeasureBitsListOption

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

/-- The progressive None path still reaches this point only after the first
count constructor. It skips just the optional comparison, not materialization. -/
theorem selected_executes (schema : Schema) (s u : ArmState) (args : Args) (bits : Packed)
    (actual : NatOperand) (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (counted : CountPost s u args schema bits base actual)
    (code : CodeAt u base) (error : read_err u = .None) (aligned : CheckSPAlignment u) :
    ∃ fuel t, run fuel u = t ∧ Prefix s t args schema bits actual ∧
      read_pc t = base + (if schema.cap.isSome then 1712#64 else 1852#64) := by
  cases schema with
  | bounded cap =>
    refine ⟨0, u, rfl, counted.prefix, ?_⟩
    simpa only [Schema.cap, Schema.countExit, Option.isSome_some, ↓reduceIte] using counted.pc
  | progressive cap =>
    let large := decide ((bits.count >>> (64 : Nat)).setWidth 64 ≠ 0#64)
    let t := ListEntry.selected cap.isSome u base
    have stackLow : 16 ≤ (r (.GPR 31#5) u).toNat := by
      have low := owned.stackLow
      rw [counted.work.stack, Args.bodySP]
      bv_omega
    have start : read_pc u = base + (if large then 1584#64 else 716#64) := by
      have input := counted.pc
      by_cases high : (bits.count >>> (64 : Nat)).setWidth 64 = 0#64 <;>
        simpa [Schema.countExit, large, high] using input
    have option : (r (.GPR 8#5) u).setWidth 32 &&& 1#32 = if cap.isSome then 1#32 else 0#32 := by
      rw [counted.work.flag]
      cases cap <;> simp only [Option.isSome_none, Option.isSome_some, ↓reduceIte] <;> decide
    have executed := ListEntry.option_run large cap.isSome u base code error aligned start option stackLow
    have memory : Delimited.MemoryFrame (Helpers.loweringWrites u) u t := by
      intro address outside
      have apart := outside ((r (.GPR 31#5) u).toNat - 16, 16) (by simp [Helpers.loweringWrites])
      have saved := (NatCompare.saved_frame u 9#5 stackLow).memory address (by dsimp at apart; omega)
      simpa only [t, ListEntry.selected, ArmState.mem_w_eq_mem] using saved
    have registers : ∀ reg : BitVec 5, r (.GPR reg) t = r (.GPR reg) u := by
      intro reg
      simp [t, ListEntry.selected, NatCompare.saved, state_simp_rules]
    have program : t.program = u.program := by
      simp [t, ListEntry.selected, NatCompare.saved, state_simp_rules]
    have sameError : read_err t = read_err u := by
      simp [t, ListEntry.selected, NatCompare.saved, state_simp_rules]
    have core := counted.prefix.core.of_registers (fun reg _ => registers reg)
    have pre := Prefix.lower_step owned counted.prefix core program sameError memory
      (fun reg _ => registers reg) (fun reg => by
        simp [t, ListEntry.selected, NatCompare.saved, state_simp_rules])
    refine ⟨(ListEntry.optionOps large cap.isSome).length, t, executed, pre, ?_⟩
    simp [t, ListEntry.selected, Schema.cap, state_simp_rules]

end SszArm.Measure.Bits.List
