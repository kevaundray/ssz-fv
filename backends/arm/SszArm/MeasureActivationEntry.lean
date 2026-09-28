import SszArm.MeasureActivationPrologue
import SszArm.MeasureOwnership

namespace SszArm.Measure

open Activation
open SszNative.Serialize (Desc Value)
open Delimited (MemoryFrame)

def argumentOps : List Op := [.p24, .p28, .p32, .p36, .p40]

@[irreducible] def arguments (s : ArmState) : ArmState := Activation.block argumentOps s

@[simp] theorem arguments_program (s : ArmState) : (arguments s).program = s.program := by
  simp [arguments, argumentOps, Activation.block]

@[simp] theorem arguments_error (s : ArmState) : read_err (arguments s) = read_err s := by
  simp [arguments, argumentOps, Activation.block]

@[simp] theorem arguments_memory (s : ArmState) : (arguments s).mem = s.mem := by
  simp [arguments, argumentOps, Activation.block, Op.effect, put, next, state_simp_rules]

@[simp] theorem arguments_pc (s : ArmState) : read_pc (arguments s) = read_pc s + 20#64 := by
  simp [arguments, argumentOps, Activation.block, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]

@[simp] theorem arguments_sp (s : ArmState) : r (.GPR 31#5) (arguments s) = r (.GPR 31#5) s := by
  simp [arguments, argumentOps, Activation.block, Op.effect, put, next, state_simp_rules]

@[simp] theorem arguments_register (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 19#5, 20#5, 21#5]) :
    r (.GPR reg) (arguments s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  simp [arguments, argumentOps, Activation.block, Op.effect, put, next,
    state_simp_rules, untouched.1, untouched.2.1, untouched.2.2.1,
    untouched.2.2.2.1, untouched.2.2.2.2]

@[simp] theorem arguments_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (arguments s) = r (.SFP reg) s := by
  simp [arguments, argumentOps, Activation.block, Op.effect, put, next, state_simp_rules]

theorem arguments_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 24#64) : run 5 s = arguments s := by
  rw [arguments]
  apply Activation.runs argumentOps s base code error
  change r .PC s = base + 24#64 at pc
  simp (config := {decide := true}) [Follows, argumentOps, Op.row, Op.effect,
    put, next, state_simp_rules, CheckSPAlignment, read_gpr,
    BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned ⊢
  exact aligned

@[irreducible] def entered (s : ArmState) : ArmState := arguments (prologue s)

@[simp] theorem entered_program (s : ArmState) : (entered s).program = s.program := by
  rw [entered, arguments_program, prologue_program]

@[simp] theorem entered_error (s : ArmState) : read_err (entered s) = read_err s := by
  rw [entered, arguments_error, prologue_error]

@[simp] theorem entered_pc (s : ArmState) : read_pc (entered s) = read_pc s + 44#64 := by
  rw [entered, arguments_pc, prologue_pc]
  simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

@[simp] theorem entered_sp (s : ArmState) : r (.GPR 31#5) (entered s) = (Args.ofEntry s).bodySP := by
  rw [entered, arguments_sp, prologue_sp]

@[simp] theorem entered_memory (s : ArmState) : (entered s).mem = (prologue s).mem := by
  rw [entered, arguments_memory]

theorem entered_frame (s : ArmState) (low : 288 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (saveWrites (Args.ofEntry s)) s (entered s) := by
  intro address outside
  rw [entered_memory]
  exact prologue_frame s low address outside

theorem entered_owned {s : ArmState} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value) : Owned (entered s) (Args.ofEntry s) desc value :=
  owned.of_save_frame (entered_frame s owned.stackLow)

theorem entered_outcome {s : ArmState} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value) :
    outcome (entered s) (Args.ofEntry s) desc value = outcome s (Args.ofEntry s) desc value :=
  outcome_eq_of_arena_eq (arenaOf_eq_of_save_frame owned (entered_frame s owned.stackLow))

theorem entered_bodyRegisters (s : ArmState) : BodyRegisters (entered s) (Args.ofEntry s) := by
  constructor
  all_goals
    simp [entered, arguments, argumentOps, Activation.block, Op.effect, put, next,
      state_simp_rules, Args.ofEntry, prologue_register, prologue_sp]

theorem entered_aligned (s : ArmState) (aligned : CheckSPAlignment s) : CheckSPAlignment (entered s) :=
  CheckSPAlignment_of_r_sp_aligned (entered_sp s) (bodySP_aligned s aligned)

theorem entered_saved (s : ArmState) (low : 288 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 offset) (entered s) =
      r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (entered_memory s))]
  exact prologue_saved s low reg offset member

theorem entered_register (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 19#5, 20#5, 21#5, 31#5]) :
    r (.GPR reg) (entered s) = r (.GPR reg) s := by
  rw [entered, arguments_register]
  · exact prologue_register s reg (by simp_all)
  · simp_all

theorem entered_vector (s : ArmState) (reg : BitVec 5) : r (.SFP reg) (entered s) = r (.SFP reg) s := by
  rw [entered, arguments_vector, prologue_vector]

theorem entered_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 11 s = entered s := by
  change run (6 + 5) s = _
  rw [run_plus, prologue_run s base code error aligned pc, entered]
  exact arguments_run _ base (code.congr (prologue_program s))
    ((prologue_error s).trans error) (prologue_aligned s aligned)
    (by simpa only [prologue_pc, pc])

theorem entered_tags {s : ArmState} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value) :
    r (.GPR 9#5) (entered s) = Emit.descriptorTag desc ∧
    r (.GPR 8#5) (entered s) = (Emit.valueTag value).setWidth 64 := by
  have prologueOwned := owned.of_save_frame (prologue_frame s owned.stackLow)
  constructor
  · simpa [entered, arguments, argumentOps, Activation.block, Op.effect, put, next,
      state_simp_rules, Args.ofEntry] using prologueOwned.descriptor.1
  · simpa [entered, arguments, argumentOps, Activation.block, Op.effect, put, next,
      state_simp_rules, Args.ofEntry] using congrArg (BitVec.setWidth 64) prologueOwned.value_at.1

end SszArm.Measure
