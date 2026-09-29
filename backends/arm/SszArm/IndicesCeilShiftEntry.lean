import SszArm.IndicesCeilShiftTail
import SszArm.IndicesCeilShiftArithmetic

set_option autoImplicit false

namespace SszArm.Indices.CeilShift.Entry

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def branch (condition : Prop) [Decidable condition] (offset : BitVec 64)
    (s : ArmState) : ArmState :=
  w .PC (if condition then read_pc s + offset else read_pc s + 4#64) s

/-- This is the actual signed-modulo amount consumed by LSLV. -/
def amount (s : ArmState) : Nat :=
  (BitVec.ofInt 6 ((r (.GPR 3#5) s).toInt % 64)).toNat

def test (value mask : BitVec 64) (s : ArmState) : ArmState :=
  let result := value &&& ~~~mask
  write_pstate (make_pstate (BitVec.extractLsb' 63 1 result)
    (if result = 0#64 then 1#1 else 0#1) 0#1 0#1) (next s)

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36
  | p40 | p44 | p48 | p52 | p80 | p84 | p88 | p92 | p96
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xaa0403e6#32)
  | .p4 => (4, 0xb4000121#32)
  | .p8 => (8, 0xb4000242#32)
  | .p12 => (12, 0xf9400029#32)
  | .p16 => (16, 0xaa0203e8#32)
  | .p20 => (20, 0x9280000a#32)
  | .p24 => (24, 0x9ac3214a#32)
  | .p28 => (28, 0xea2a013f#32)
  | .p32 => (32, 0x54000221#32)
  | .p36 => (36, 0x14000039#32)
  | .p40 => (40, 0x92800008#32)
  | .p44 => (44, 0x9ac32108#32)
  | .p48 => (48, 0xea28005f#32)
  | .p52 => (52, 0x540006a0#32)
  | .p80 => (80, 0xaa1f03e8#32)
  | .p84 => (84, 0x9280000a#32)
  | .p88 => (88, 0x9ac3214a#32)
  | .p92 => (92, 0xea2a03ff#32)
  | .p96 => (96, 0x54000540#32)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 6#5 (r (.GPR 4#5) s) s
  | .p4, s => branch (r (.GPR 1#5) s = 0#64) 36#64 s
  | .p8, s => branch (r (.GPR 2#5) s = 0#64) 72#64 s
  | .p12, s => put 9#5 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p16, s => put 8#5 (r (.GPR 2#5) s) s
  | .p20, s | .p84, s => put 10#5 (-1) s
  | .p24, s | .p88, s => put 10#5 (r (.GPR 10#5) s <<< amount s) s
  | .p28, s => test (r (.GPR 9#5) s) (r (.GPR 10#5) s) s
  | .p32, s => branch (r (.FLAG .Z) s ≠ 1#1) 68#64 s
  | .p36, s => w .PC (read_pc s + 228#64) s
  | .p40, s => put 8#5 (-1) s
  | .p44, s => put 8#5 (r (.GPR 8#5) s <<< amount s) s
  | .p48, s => test (r (.GPR 2#5) s) (r (.GPR 8#5) s) s
  | .p52, s => branch (r (.FLAG .Z) s = 1#1) 212#64 s
  | .p80, s => put 8#5 0#64 s
  | .p92, s => test 0#64 (r (.GPR 10#5) s) s
  | .p96, s => branch (r (.FLAG .Z) s = 1#1) 168#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.CeilShift.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.CeilShift.chunk0_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at entry fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, branch, amount, test, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, zero_flag_spec,
        BitVec.setWidth_eq, apply_ite]
  all_goals try (apply w_of_w_commute <;> decide)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, branch, test, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, branch, test, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.CeilShift.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change run (ops.length + 1) s = block ops (op.effect s)
      rw [run, step op s base code error follows.1]
      exact ih _ (Codec.Linked.WordsAt.preserve code (op.program s))
        ((op.error s).trans error) follows.2

/-- The original entry copies the actual arena register before classifying the
raw Nat header. In particular empty Large is not confused with Small zero. -/
theorem original_entry (s : ArmState) (base : BitVec 64)
    (code : Linked.CeilShift.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base) :
    run 2 s = block [.p0, .p4] s := by
  exact runs [.p0, .p4] s base code error
    (by simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, entry])

theorem dispatch_pc (s : ArmState) (base : BitVec 64) (entry : read_pc s = base) :
    read_pc (block [.p0, .p4] s) =
      if r (.GPR 1#5) s = 0#64 then base + 40#64 else base + 8#64 := by
  simp [block, Op.effect, put, next, branch, state_simp_rules, entry, BitVec.add_assoc]

/-- The source-provided shift bound also identifies the literal LSLV amount. -/
theorem amount_eq (s : ArmState) (bits : Nat) (bounded : bits ≤ 8)
    (input : r (.GPR 3#5) s = BitVec.ofNat 64 bits) : amount s = bits := by
  have cases : bits = 0 ∨ bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨
      bits = 5 ∨ bits = 6 ∨ bits = 7 ∨ bits = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [amount, input] <;> decide

/-- Both Small and loaded Large masks use this exact source remainder. -/
theorem tested_word (s : ArmState) (value : BitVec 64) (bits : Nat)
    (bounded : bits ≤ 8) (input : r (.GPR 3#5) s = BitVec.ofNat 64 bits) :
    value &&& ~~~((-1 : BitVec 64) <<< amount s) =
      value &&& SszNative.Indices.lowMask bits := by
  rw [amount_eq s bits bounded input]
  simpa only [Nat.mod_eq_of_lt (show bits < 64 by omega)] using
    low_mask_test value bits bounded

theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change (block ops (op.effect s)).program = s.program
      rw [ih, op.program]

theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change read_err (block ops (op.effect s)) = read_err s
      rw [ih, op.error]

/-- Raw Small no-remainder path, from the original entry all the way to the
real Nat::shr entry; the source input and original link register are retained. -/
theorem small_tail (s : ArmState) (bias : BitVec 64)
    (code : Linked.CeilShift.CodeAt s (bias + 2263988#64))
    (error : read_err s = .None) (entry : read_pc s = bias + 2263988#64)
    (small : r (.GPR 1#5) s = 0#64)
    (zero : r (.GPR 2#5) s &&& ~~~((-1 : BitVec 64) <<< amount s) = 0#64) :
    run 9 s = Tail.target (block [.p0, .p4, .p40, .p44, .p48, .p52] s) bias := by
  let ops : List Op := [.p0, .p4, .p40, .p44, .p48, .p52]
  have path : Follows (bias + 2263988#64) ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, branch, test, amount,
      state_simp_rules, entry, small, BitVec.add_assoc]
  have executed : run 6 s = block ops s := runs ops s _ code error path
  have tailPC : read_pc (block ops s) = bias + 2264252#64 := by
    simp [ops, block, Op.effect, put, next, branch, test, amount,
      state_simp_rules, entry, small, BitVec.add_assoc] at zero ⊢
    simp [zero]
  have tailCode : Linked.CeilShift.CodeAt (block ops s) (bias + 2263988#64) :=
    Codec.Linked.WordsAt.preserve code (block_program ops s)
  rw [show 9 = 6 + 3 by decide, run_plus, executed]
  exact Tail.run_tail _ bias tailCode ((block_error ops s).trans error) tailPC

/-- A physically empty Large goes directly to shr. No source load occurs on
this path, so the nonzero pointer is allowed to be an empty-slice sentinel. -/
theorem empty_tail (s : ArmState) (bias : BitVec 64)
    (code : Linked.CeilShift.CodeAt s (bias + 2263988#64))
    (error : read_err s = .None) (entry : read_pc s = bias + 2263988#64)
    (large : r (.GPR 1#5) s ≠ 0#64) (empty : r (.GPR 2#5) s = 0#64) :
    run 11 s = Tail.target (block [.p0, .p4, .p8, .p80, .p84, .p88, .p92, .p96] s) bias := by
  let ops : List Op := [.p0, .p4, .p8, .p80, .p84, .p88, .p92, .p96]
  have path : Follows (bias + 2263988#64) ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, branch, test, amount,
      state_simp_rules, entry, large, empty, BitVec.add_assoc]
  have executed : run 8 s = block ops s := runs ops s _ code error path
  have tailPC : read_pc (block ops s) = bias + 2264252#64 := by
    simp [ops, block, Op.effect, put, next, branch, test, amount,
      state_simp_rules, entry, large, empty, BitVec.add_assoc]
  have tailCode : Linked.CeilShift.CodeAt (block ops s) (bias + 2263988#64) :=
    Codec.Linked.WordsAt.preserve code (block_program ops s)
  rw [show 11 = 8 + 3 by decide, run_plus, executed]
  exact Tail.run_tail _ bias tailCode ((block_error ops s).trans error) tailPC

/-- Nonempty Large tests exactly its first stored limb, not its declared bit
length or a normalized replacement of the original raw operand. -/
theorem large_tail (s : ArmState) (bias : BitVec 64)
    (code : Linked.CeilShift.CodeAt s (bias + 2263988#64))
    (error : read_err s = .None) (entry : read_pc s = bias + 2263988#64)
    (large : r (.GPR 1#5) s ≠ 0#64) (nonempty : r (.GPR 2#5) s ≠ 0#64)
    (zero : read_mem_bytes 8 (r (.GPR 1#5) s) s &&&
      ~~~((-1 : BitVec 64) <<< amount s) = 0#64) :
    run 13 s = Tail.target
      (block [.p0, .p4, .p8, .p12, .p16, .p20, .p24, .p28, .p32, .p36] s) bias := by
  let ops : List Op := [.p0, .p4, .p8, .p12, .p16, .p20, .p24, .p28, .p32, .p36]
  have path : Follows (bias + 2263988#64) ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, branch, test, amount,
      state_simp_rules, entry, large, nonempty, BitVec.add_assoc] at zero ⊢
    simp [zero]
  have executed : run 10 s = block ops s := runs ops s _ code error path
  have tailPC : read_pc (block ops s) = bias + 2264252#64 := by
    simp [ops, block, Op.effect, put, next, branch, test, amount,
      state_simp_rules, entry, large, nonempty, BitVec.add_assoc] at zero ⊢
    simp [zero]
  have tailCode : Linked.CeilShift.CodeAt (block ops s) (bias + 2263988#64) :=
    Codec.Linked.WordsAt.preserve code (block_program ops s)
  rw [show 13 = 10 + 3 by decide, run_plus, executed]
  exact Tail.run_tail _ bias tailCode ((block_error ops s).trans error) tailPC

end SszArm.Indices.CeilShift.Entry
