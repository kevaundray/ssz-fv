import SszArm.EmitActivationEntry
import SszArm.EmitDispatch

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)
open Delimited (MemoryFrame)

@[irreducible] def routed (s : ArmState) (desc : Desc) : ArmState := selected (entered s) desc

/-- Derived internal state: no member of this structure is a public entry
precondition. All observations and saved activation originate at private entry0. -/
structure Routed (s t : ArmState) (desc : Desc) (value : Value) (size : Nat) (base : BitVec 64) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64 (bodyEntry desc)
  code : CodeAt t base
  error : read_err t = .None
  aligned : CheckSPAlignment t
  owned : Owned t (Args.ofEntry s) desc value size
  registers : BodyRegisters t (Args.ofEntry s)
  descriptor : r (.GPR 1#5) t = (Args.ofEntry s).descriptor
  tag : r (.GPR 8#5) t = descriptorTag desc
  valueTag : r (.GPR 9#5) t = (Emit.valueTag value).setWidth 64
  program : t.program = s.program
  frame : MemoryFrame (stackWrites (Args.ofEntry s)) s t
  saved : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 offset) t = r (.GPR reg) s
  untouched : ∀ reg : BitVec 5, reg ∈ [18#5, 28#5, 29#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem entry_to_body (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value) (size : Nat)
    (owned : Owned s (Args.ofEntry s) desc value size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    run (12 + (dispatchOps desc).length) s = routed s desc ∧
    Routed s (routed s desc) desc value size base := by
  obtain ⟨tag, valueTag⟩ := entered_tags owned
  have compatible := compatible_of_expected owned.expected
  have enteredPC : read_pc (entered s) = base + 48#64 := by rw [entered_pc, pc]
  have enteredCode : CodeAt (entered s) base := by simpa only [CodeAt, entered_program] using code
  have enteredError := (entered_error s).trans error
  constructor
  · rw [run_plus, entered_run s base code error aligned pc, routed]
    exact selected_run _ base desc value compatible enteredCode enteredError enteredPC tag valueTag
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [routed]
      exact selected_pc _ base desc value compatible enteredPC tag valueTag
    · simpa only [CodeAt, routed, selected_program, entered_program] using code
    · simpa only [routed, selected_error] using enteredError
    · rw [routed]
      exact selected_aligned _ desc (entered_aligned s aligned)
    · exact (entered_owned owned).of_mem_eq (by rw [routed, selected_memory])
    · rw [routed]
      exact selected_bodyRegisters desc (entered_bodyRegisters s)
    · rw [routed, selected_register, entered_register s 1#5 (by decide)]
      rfl
    · simpa only [routed, selected_register] using tag
    · simpa only [routed, selected_register] using valueTag
    · rw [routed, selected_program, entered_program]
    · intro address outside
      rw [routed, selected_memory]
      exact entered_frame s owned.stackLow address outside
    · intro reg offset member
      rw [routed, (Memory.mem_eq_iff_read_mem_bytes_eq.mp (selected_memory (entered s) desc))]
      exact entered_saved s owned.stackLow reg offset member
    · intro reg member
      rw [routed, selected_register]
      apply entered_register
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · intro reg
      rw [routed, selected_vector, entered_vector]

end SszArm.Emit
