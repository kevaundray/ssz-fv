import SszArm.MeasureActivationEntry
import SszArm.MeasureEntryDispatch

namespace SszArm.Measure

open SszNative.Serialize (Desc Value)
open Delimited (MemoryFrame)

@[irreducible] def routed (s : ArmState) (desc : Desc) : ArmState := selected (entered s) desc

/-- Derived from original entry, for every primitive value including wrong-type
cases. No semantic success, future helper state, or retained-plan branch is assumed. -/
structure Routed (s t : ArmState) (desc : Desc) (value : Value) (base : BitVec 64) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64 (bodyEntry desc)
  code : CodeAt t base
  error : read_err t = .None
  aligned : CheckSPAlignment t
  owned : Owned t (Args.ofEntry s) desc value
  registers : BodyRegisters t (Args.ofEntry s)
  descriptor : r (.GPR 1#5) t = (Args.ofEntry s).descriptor
  tag : r (.GPR 9#5) t = Emit.descriptorTag desc
  valueTag : r (.GPR 8#5) t = (Emit.valueTag value).setWidth 64
  program : t.program = s.program
  frame : MemoryFrame (saveWrites (Args.ofEntry s)) s t
  saved : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 offset) t = r (.GPR reg) s
  untouched : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  arena : arenaOf t (Args.ofEntry s) = arenaOf s (Args.ofEntry s)

theorem Routed.outcome {s t : ArmState} {desc : Desc} {value : Value} {base : BitVec 64}
    (route : Routed s t desc value base) :
    outcome t (Args.ofEntry s) desc value = outcome s (Args.ofEntry s) desc value :=
  outcome_eq_of_arena_eq route.arena

theorem routed_frame (s : ArmState) (desc : Desc) (low : 288 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (saveWrites (Args.ofEntry s)) s (routed s desc) := by
  intro address outside
  rw [routed, selected_memory]
  exact entered_frame s low address outside

theorem entry_to_body (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    run (11 + (dispatchOps desc).length) s = routed s desc ∧
    Routed s (routed s desc) desc value base := by
  obtain ⟨tag, valueTag⟩ := entered_tags owned
  have enteredPC : read_pc (entered s) = base + 44#64 := by rw [entered_pc, pc]
  have enteredCode : CodeAt (entered s) base := code.congr (entered_program s)
  have enteredError := (entered_error s).trans error
  constructor
  · rw [run_plus, entered_run s base code error aligned pc, routed]
    exact selected_run _ base desc enteredCode enteredError enteredPC tag
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [routed]
      exact selected_pc _ base desc enteredPC tag
    · exact code.congr (by rw [routed, selected_program, entered_program])
    · simpa only [routed, selected_error] using enteredError
    · rw [routed]
      exact selected_aligned _ desc (entered_aligned s aligned)
    · exact owned.of_save_frame (routed_frame s desc owned.stackLow)
    · rw [routed]
      exact selected_bodyRegisters desc (entered_bodyRegisters s)
    · rw [routed, selected_register _ _ _ (by decide), entered_register s 1#5 (by decide)]
      rfl
    · simpa only [routed, selected_register (entered s) desc 9#5 (by decide)] using tag
    · simpa only [routed, selected_register (entered s) desc 8#5 (by decide)] using valueTag
    · rw [routed, selected_program, entered_program]
    · exact routed_frame s desc owned.stackLow
    · intro reg offset member
      rw [routed, (Memory.mem_eq_iff_read_mem_bytes_eq.mp (selected_memory (entered s) desc))]
      exact entered_saved s owned.stackLow reg offset member
    · intro reg member
      have different : reg ≠ 22#5 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      rw [routed, selected_register _ _ _ different]
      apply entered_register
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    · intro reg
      rw [routed, selected_vector, entered_vector]
    · exact arenaOf_eq_of_save_frame owned (routed_frame s desc owned.stackLow)

end SszArm.Measure
