import SszArm.CodecMeasureSingletonOps
import SszArm.CodecLinkedMeasureParts

set_option autoImplicit false

namespace SszArm.Codec.Measure.PartsReserve

open SszArm.Udivti3 (next put flagged branch)

inductive Op where
  | loadBase | loadUsed | addAddress | addressGuard | compareAlignment | alignmentGuard
  | addPadding | maskPadding | subtractAddress | addUsed | usedGuard
  | multiplyFive | multiplyEight | addSize | sizeGuard | loadCapacity
  | compareCapacity | capacityGuard | zeroIndex | addPointer | resultPointer | firstSlot | commit
  deriving DecidableEq

def Op.pc : Op → Nat
  | .loadBase => 364 | .loadUsed => 368 | .addAddress => 372 | .addressGuard => 376
  | .compareAlignment => 380 | .alignmentGuard => 384 | .addPadding => 388
  | .maskPadding => 392 | .subtractAddress => 396 | .addUsed => 400 | .usedGuard => 404
  | .multiplyFive => 408 | .multiplyEight => 412 | .addSize => 416 | .sizeGuard => 420
  | .loadCapacity => 424 | .compareCapacity => 428 | .capacityGuard => 432
  | .zeroIndex => 436 | .addPointer => 440 | .resultPointer => 444 | .firstSlot => 448
  | .commit => 452

def Op.word : Op → BitVec 32
  | .loadBase => 0xf9400288#32 | .loadUsed => 0xf9400a8a#32
  | .addAddress => 0xab08014b#32 | .addressGuard => 0x54001242#32
  | .compareAlignment => 0xb100217f#32 | .alignmentGuard => 0x54001208#32
  | .addPadding => 0x91001d69#32 | .maskPadding => 0x927df129#32
  | .subtractAddress => 0xcb0b012b#32 | .addUsed => 0xab0a016a#32
  | .usedGuard => 0x54001162#32 | .multiplyFive => 0x8b1a0b4b#32
  | .multiplyEight => 0xd37df16b#32 | .addSize => 0xab0b014b#32
  | .sizeGuard => 0x540010e2#32 | .loadCapacity => 0xf940068c#32
  | .compareCapacity => 0xeb0c017f#32 | .capacityGuard => 0x54001088#32
  | .zeroIndex => 0xaa1f03f7#32 | .addPointer => 0x8b0a0118#32
  | .resultPointer => 0x910343f9#32 | .firstSlot => 0x9100413d#32
  | .commit => 0xf9000a8b#32

def effect : Op → ArmState → ArmState
  | .loadBase, s => put 8 (read_mem_bytes 8 (r (.GPR 20) s) s) s
  | .loadUsed, s => put 10 (read_mem_bytes 8 (r (.GPR 20) s + 16#64) s) s
  | .addAddress, s => flagged 11 (r (.GPR 10) s) (r (.GPR 8) s) 0#1 s
  | .addressGuard, s => branch (r (.FLAG .C) s = 1#1) 584#64 s
  | .compareAlignment, s =>
      write_pstate (AddWithCarry (r (.GPR 11) s) 8#64 0#1).2 (next s)
  | .alignmentGuard, s =>
      branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 576#64 s
  | .addPadding, s => put 9 (r (.GPR 11) s + 7#64) s
  | .maskPadding, s => put 9 (r (.GPR 9) s &&& ~~~7#64) s
  | .subtractAddress, s => put 11 (r (.GPR 9) s - r (.GPR 11) s) s
  | .addUsed, s => flagged 10 (r (.GPR 11) s) (r (.GPR 10) s) 0#1 s
  | .usedGuard, s => branch (r (.FLAG .C) s = 1#1) 556#64 s
  | .multiplyFive, s => put 11 (r (.GPR 26) s + (r (.GPR 26) s <<< (2 : Nat))) s
  | .multiplyEight, s => put 11 (r (.GPR 11) s <<< (3 : Nat)) s
  | .addSize, s => flagged 11 (r (.GPR 10) s) (r (.GPR 11) s) 0#1 s
  | .sizeGuard, s => branch (r (.FLAG .C) s = 1#1) 540#64 s
  | .loadCapacity, s => put 12 (read_mem_bytes 8 (r (.GPR 20) s + 8#64) s) s
  | .compareCapacity, s => Udivti3.compare (r (.GPR 11) s) (r (.GPR 12) s) s
  | .capacityGuard, s =>
      branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 528#64 s
  | .zeroIndex, s => put 23 0#64 s
  | .addPointer, s => put 24 (r (.GPR 8) s + r (.GPR 10) s) s
  | .resultPointer, s => put 25 (r (.GPR 31) s + 208#64) s
  | .firstSlot, s => put 29 (r (.GPR 9) s + 16#64) s
  | .commit, s => next (write_mem_bytes 8 (r (.GPR 20) s + 16#64) (r (.GPR 11) s) s)

theorem step_word (op : Op) (s : ArmState) (error : read_err s = .None)
    (fetch : s.program.find? (read_pc s) = some op.word) : stepi s = effect op s := by
  cases op <;> simp only [Op.word] at fetch
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
      (fetch_inst_from_program.trans fetch) rfl]
    simp (config := {decide := true, instances := true})
      [effect, next, put, Udivti3.compare, flagged, branch, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, UintCodec.uint_lsl3_mask, UintCodec.uint_and_ones, apply_ite]
    all_goals try (split <;> simp_all)
    all_goals apply w_of_w_commute <;> decide

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ op : Op, s.program.find? (base + BitVec.ofNat 64 op.pc) = some op.word

theorem code_of_linked (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureParts.CodeAt s base) : CodeAt s base := by
  intro op
  apply Linked.MeasureParts.chunk1_codeAt code (op.pc, op.word)
  cases op <;> decide

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.pc) : stepi s = effect op s := by
  apply step_word op s error
  rw [pc]
  exact code op

theorem effect_program (op : Op) (s : ArmState) : (effect op s).program = s.program := by
  cases op <;> simp [effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem effect_error (op : Op) (s : ArmState) : read_err (effect op s) = read_err s := by
  cases op <;> simp [effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

def Preserved : StateField → Prop
  | .GPR reg => reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 10#5 ∧ reg ≠ 11#5 ∧ reg ≠ 12#5 ∧
      reg ≠ 23#5 ∧ reg ≠ 24#5 ∧ reg ≠ 25#5 ∧ reg ≠ 29#5
  | .ERR | .SFP _ => True
  | .PC | .FLAG _ => False

theorem effect_field (op : Op) (s : ArmState) (field : StateField)
    (preserved : Preserved field) : r field (effect op s) = r field s := by
  cases op <;> cases field <;>
    simp_all (config := {decide := true})
      [Preserved, effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem effect_memory (op : Op) (s : ArmState) (notCommit : op ≠ .commit) :
    (effect op s).mem = s.mem := by
  cases op <;> simp_all [effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

def block : List Op → ArmState → ArmState
  | [], s => s
  | op :: rest, s => block rest (effect op s)

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = base + BitVec.ofNat 64 op.pc ∧
      Follows base rest (effect op s)

theorem block_program (ops : List Op) (s : ArmState) : (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (effect_program op s)

theorem block_error (ops : List Op) (s : ArmState) : read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (effect_error op s)

theorem block_field (ops : List Op) (s : ArmState) (field : StateField)
    (preserved : Preserved field) : r field (block ops s) = r field s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (effect_field op s field preserved)

theorem block_memory (ops : List Op) (s : ArmState) (notCommit : Op.commit ∉ ops) :
    (block ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    have notOp : op ≠ .commit := by intro equal; apply notCommit; simp [equal]
    have notRest : Op.commit ∉ rest := fun member => notCommit (List.mem_cons_of_mem _ member)
    exact (ih _ notRest).trans (effect_memory op s notOp)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨pc, later⟩ := follows
    rw [List.length_cons, Nat.add_comm rest.length 1, run_plus]
    change run rest.length (stepi s) = block rest (effect op s)
    rw [step op s base code error pc]
    apply ih _ _ ((effect_error op s).trans error) later
    intro instruction
    simpa only [effect_program] using code instruction

end SszArm.Codec.Measure.PartsReserve
