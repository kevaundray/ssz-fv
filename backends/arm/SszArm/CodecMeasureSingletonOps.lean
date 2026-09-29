import SszArm.UintArenaProofs

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open SszArm.Udivti3 (next put flagged branch)

/-- The allocator instructions at the linked `plan_singleton` entry. The
prologue and copy/return continuation are separate execution blocks. -/
inductive Op where
  | loadBase | loadUsed | saveResult | addAddress | addressGuard
  | compareAlignment | alignmentGuard | addPadding | maskPadding
  | subtractAddress | addUsed | usedGuard | compareSize | sizeGuard
  | loadCapacity | addSize | compareCapacity | capacityGuard
  | addPointer | commit
  deriving DecidableEq

def Op.pc : Op → Nat
  | .loadBase => 12 | .loadUsed => 16 | .saveResult => 20
  | .addAddress => 24 | .addressGuard => 28
  | .compareAlignment => 32 | .alignmentGuard => 36
  | .addPadding => 40 | .maskPadding => 44 | .subtractAddress => 48
  | .addUsed => 52 | .usedGuard => 56 | .compareSize => 60 | .sizeGuard => 64
  | .loadCapacity => 68 | .addSize => 72 | .compareCapacity => 76
  | .capacityGuard => 80 | .addPointer => 84 | .commit => 88

def Op.word : Op → BitVec 32
  | .loadBase => 0xf9400028#32 | .loadUsed => 0xf9400829#32
  | .saveResult => 0xaa0003f3#32 | .addAddress => 0xab08012a#32
  | .addressGuard => 0x54000462#32 | .compareAlignment => 0xb100215f#32
  | .alignmentGuard => 0x54000428#32 | .addPadding => 0x91001d4b#32
  | .maskPadding => 0x927df16b#32 | .subtractAddress => 0xcb0a016a#32
  | .addUsed => 0xab090149#32 | .usedGuard => 0x54000382#32
  | .compareSize => 0xb100a53f#32 | .sizeGuard => 0x54000348#32
  | .loadCapacity => 0xf940042b#32 | .addSize => 0x9100a12a#32
  | .compareCapacity => 0xeb0b015f#32 | .capacityGuard => 0x540002c8#32
  | .addPointer => 0x8b090114#32 | .commit => 0xf900082a#32

def effect : Op → ArmState → ArmState
  | .loadBase, s => put 8 (read_mem_bytes 8 (r (.GPR 1) s) s) s
  | .loadUsed, s => put 9 (read_mem_bytes 8 (r (.GPR 1) s + 16#64) s) s
  | .saveResult, s => put 19 (r (.GPR 0) s) s
  | .addAddress, s => flagged 10 (r (.GPR 9) s) (r (.GPR 8) s) 0#1 s
  | .addressGuard, s => branch (r (.FLAG .C) s = 1#1) 140#64 s
  | .compareAlignment, s =>
      write_pstate (AddWithCarry (r (.GPR 10) s) 8#64 0#1).2 (next s)
  | .alignmentGuard, s =>
      branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 132#64 s
  | .addPadding, s => put 11 (r (.GPR 10) s + 7#64) s
  | .maskPadding, s => put 11 (r (.GPR 11) s &&& ~~~7#64) s
  | .subtractAddress, s => put 10 (r (.GPR 11) s - r (.GPR 10) s) s
  | .addUsed, s => flagged 9 (r (.GPR 10) s) (r (.GPR 9) s) 0#1 s
  | .usedGuard, s => branch (r (.FLAG .C) s = 1#1) 112#64 s
  | .compareSize, s =>
      write_pstate (AddWithCarry (r (.GPR 9) s) 41#64 0#1).2 (next s)
  | .sizeGuard, s =>
      branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 104#64 s
  | .loadCapacity, s => put 11 (read_mem_bytes 8 (r (.GPR 1) s + 8#64) s) s
  | .addSize, s => put 10 (r (.GPR 9) s + 40#64) s
  | .compareCapacity, s => Udivti3.compare (r (.GPR 10) s) (r (.GPR 11) s) s
  | .capacityGuard, s =>
      branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 88#64 s
  | .addPointer, s => put 20 (r (.GPR 8) s + r (.GPR 9) s) s
  | .commit, s =>
      next (write_mem_bytes 8 (r (.GPR 1) s + 16#64) (r (.GPR 10) s) s)

/-- Word-local execution does not assume which guard succeeds. -/
theorem step_word (op : Op) (s : ArmState)
    (error : read_err s = .None)
    (fetch : s.program.find? (read_pc s) = some op.word) :
    stepi s = effect op s := by
  cases op <;> simp only [Op.word] at fetch
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
      (fetch_inst_from_program.trans fetch) rfl]
    simp (config := {decide := true, instances := true})
      [effect, next, put, Udivti3.compare, flagged, branch, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, apply_ite]
    all_goals try (split <;> simp_all)
    all_goals apply w_of_w_commute <;> decide

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ op : Op, s.program.find? (base + BitVec.ofNat 64 op.pc) = some op.word

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.pc) :
    stepi s = effect op s := by
  apply step_word op s error
  rw [pc]
  exact code op

theorem effect_program (op : Op) (s : ArmState) :
    (effect op s).program = s.program := by
  cases op <;>
    simp [effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem effect_error (op : Op) (s : ArmState) :
    read_err (effect op s) = read_err s := by
  cases op <;>
    simp [effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem effect_code (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) : CodeAt (effect op s) base := by
  intro instruction
  simpa only [effect_program] using code instruction

def Preserved : StateField → Prop
  | .GPR reg => reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 10#5 ∧ reg ≠ 11#5 ∧
      reg ≠ 19#5 ∧ reg ≠ 20#5
  | .ERR | .SFP _ => True
  | .PC | .FLAG _ => False

theorem effect_field (op : Op) (s : ArmState) (field : StateField)
    (preserved : Preserved field) : r field (effect op s) = r field s := by
  cases op <;> cases field <;>
    simp_all (config := {decide := true})
      [Preserved, effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem effect_memory (op : Op) (s : ArmState) (notCommit : op ≠ .commit) :
    (effect op s).mem = s.mem := by
  cases op <;>
    simp_all [effect, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

def block : List Op → ArmState → ArmState
  | [], s => s
  | op :: rest, s => block rest (effect op s)

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = base + BitVec.ofNat 64 op.pc ∧
      Follows base rest (effect op s)

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
    exact ih _ (effect_code op s base code) ((effect_error op s).trans error) later

end SszArm.Codec.Measure.Singleton
