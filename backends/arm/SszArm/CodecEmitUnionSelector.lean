import SszArm.CodecLinkedEmit
import SszArm.EmitActivationReturnOps
import SszArm.EmitDispatchOps

namespace SszArm.Codec.Emit.Union

open SszArm.Emit.Activation (next put)
open SszArm.Emit.ReturnBlock (restore)
open SszArm.Emit.Dispatch (branch)
open SszNative (NatOperand)

inductive Op where
  | p768 | p772 | p776 | p780 | p784 | p788 | p792 | p1588 | p1592
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p768 => (768, 0xb4002555#32)
  | .p772 => (772, 0xa940e2d7#32)
  | .p776 => (776, 0xaa1803e8#32)
  | .p780 => (780, 0xb4001977#32)
  | .p784 => (784, 0xb4001938#32)
  | .p788 => (788, 0xf94002e8#32)
  | .p792 => (792, 0x140000c8#32)
  | .p1588 => (1588, 0xaa1f03e8#32)
  | .p1592 => (1592, 0x39000288#32)

def Op.effect : Op → ArmState → ArmState
  | .p768, s => branch (r (.GPR 21#5) s = 0#64) 1192#64 s
  | .p772, s =>
      w (.GPR 24#5) (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s)
        (put 23 (read_mem_bytes 8 (r (.GPR 22#5) s + 8#64) s) s)
  | .p776, s => put 8 (r (.GPR 24#5) s) s
  | .p780, s => branch (r (.GPR 23#5) s = 0#64) 812#64 s
  | .p784, s => branch (r (.GPR 24#5) s = 0#64) 804#64 s
  | .p788, s => put 8 (read_mem_bytes 8 (r (.GPR 23#5) s) s) s
  | .p792, s => w .PC (read_pc s + 800#64) s
  | .p1588, s => put 8 0#64 s
  | .p1592, s => next (write_mem_bytes 1 (r (.GPR 20#5) s) ((r (.GPR 8#5) s).setWidth 8) s)

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched : s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
    cases op <;> first
      | exact Linked.Emit.chunk3_codeAt code _ (by decide)
      | exact Linked.Emit.chunk6_codeAt code _ (by decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, branch, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, BitVec.setWidth_eq, BoolCodec.pair_read_low,
       BoolCodec.pair_read_high, BitVec.add_assoc, apply_ite]
  all_goals first
    | exact w_of_w_commute (by decide)
    | simp only [w, write_base_pc, write_base_gpr]
    | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

@[simp] theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 23#5, 24#5]) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at untouched
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules,
    untouched.1, untouched.2.1, untouched.2.2]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1]
    exact ih _ (Linked.WordsAt.preserve code (op.program s))
      ((op.error s).trans error) follows.2

def lowWord : NatOperand → BitVec 64
  | .small word => word
  | .large _ [] => 0
  | .large _ (word :: _) => word

theorem lowWord_byte (selector : NatOperand) :
    UInt8.ofBitVec ((lowWord selector).setWidth 8) = UInt8.ofNat selector.value := by
  have narrow (word : BitVec 64) :
      UInt8.ofBitVec (word.setWidth 8) = UInt8.ofNat word.toNat := by
    apply UInt8.toBitVec_inj.mp
    change word.setWidth 8 = BitVec.ofNat 8 word.toNat
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  have byte := SszNative.Limbs.byteAt_eq_value selector.words 0
  cases selector with
  | small word =>
    rw [show lowWord (.small word) = word from rfl, narrow]
    simp [NatOperand.value, NatOperand.words, SszNative.Limbs.value]
  | large pointer words =>
    cases words with
    | nil => rfl
    | cons word rest =>
      have low : UInt8.ofNat word.toNat =
          UInt8.ofNat (SszNative.Limbs.value (word :: rest) % 256) := by
        simpa [NatOperand.words, SszNative.Limbs.byteAt] using byte
      exact (narrow word).trans (low.trans UInt8.ofNat_mod_size)

def selectorOps : NatOperand → List Op
  | .small _ => [.p768, .p772, .p776, .p780, .p1592]
  | .large _ [] => [.p768, .p772, .p776, .p780, .p784, .p1588, .p1592]
  | .large _ (_ :: _) => [.p768, .p772, .p776, .p780, .p784, .p788, .p792, .p1592]

/-- Only observations of the original Nat are needed to choose its low byte;
large empty and padded representations are not normalized or rejected. -/
structure SelectorAt (s : ArmState) (selector : NatOperand) : Prop where
  pointer : read_mem_bytes 8 (r (.GPR 22#5) s + 8#64) s = selector.pointer
  payload : read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s = selector.payload
  borrowed : selector.At (UintCodec.widthLoad s)

private theorem borrowed_nonzero {s : ArmState} {pointer : BitVec 64} {words : List (BitVec 64)}
    (borrowed : (NatOperand.large pointer words).At (UintCodec.widthLoad s)) : pointer ≠ 0#64 := by
  have positive := borrowed.1
  intro zero
  simp only [zero, BitVec.toNat_ofNat] at positive
  omega

private theorem borrowed_first {s : ArmState} {pointer word : BitVec 64} {rest : List (BitVec 64)}
    (borrowed : (NatOperand.large pointer (word :: rest)).At (UintCodec.widthLoad s)) :
    read_mem_bytes 8 pointer s = word := by
  have first := borrowed.2.2.2 (⟨0, by simp⟩ : Fin (word :: rest).length)
  change UintCodec.widthLoad s pointer.toNat 8 = some word.toNat at first
  apply BitVec.eq_of_toNat_eq
  simpa only [UintCodec.widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Option.some.injEq] using first

theorem selector_follows (s : ArmState) (base : BitVec 64) (selector : NatOperand)
    (pc : read_pc s = base + 768#64) (available : r (.GPR 21#5) s ≠ 0#64)
    (stored : SelectorAt s selector) : Follows base (selectorOps selector) s := by
  change r .PC s = _ at pc
  cases selector with
  | small word =>
    simp (config := {decide := true}) [selectorOps, Follows, Op.row, Op.effect,
      next, put, branch, state_simp_rules, pc, available, stored.pointer, stored.payload,
      NatOperand.pointer, NatOperand.payload, BitVec.add_assoc]
  | large pointer words =>
    have pointerNonzero := borrowed_nonzero stored.borrowed
    have countBound : words.length < 2 ^ 64 := by
      have physical := stored.borrowed.2.2.1
      omega
    cases words with
    | nil =>
      simp (config := {decide := true}) [selectorOps, Follows, Op.row, Op.effect,
        next, put, branch, state_simp_rules, pc, available, stored.pointer, stored.payload,
        NatOperand.pointer, NatOperand.payload, pointerNonzero, BitVec.add_assoc]
    | cons word rest =>
      have countNonzero : BitVec.ofNat 64 (word :: rest).length ≠ 0#64 := by
        intro zero
        have := congrArg BitVec.toNat zero
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at this
        simp at this
      simp only [List.length_cons] at countNonzero
      have first := borrowed_first stored.borrowed
      simp (config := {decide := true}) [selectorOps, Follows, Op.row, Op.effect,
        next, put, branch, state_simp_rules, pc, available, stored.pointer, stored.payload,
        NatOperand.pointer, NatOperand.payload, pointerNonzero, countNonzero,
        first, BitVec.add_assoc]

theorem selector_run (s : ArmState) (base : BitVec 64) (selector : NatOperand)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 768#64) (available : r (.GPR 21#5) s ≠ 0#64)
    (stored : SelectorAt s selector) :
    run (selectorOps selector).length s = block (selectorOps selector) s :=
  runs _ s base code error (selector_follows s base selector pc available stored)

theorem selector_memory (s : ArmState) (selector : NatOperand)
    (stored : SelectorAt s selector) :
    (block (selectorOps selector) s).mem =
      (write_mem_bytes 1 (r (.GPR 20#5) s) ((lowWord selector).setWidth 8) s).mem := by
  cases selector with
  | small word =>
    simp [selectorOps, block, Op.effect, put, next, branch, lowWord,
      state_simp_rules, stored.pointer, stored.payload, NatOperand.pointer, NatOperand.payload]
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]
  | large pointer words =>
    cases words with
    | nil =>
      simp [selectorOps, block, Op.effect, put, next, branch, lowWord, state_simp_rules]
      simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]
    | cons word rest =>
      have first := borrowed_first stored.borrowed
      simp [selectorOps, block, Op.effect, put, next, branch, lowWord,
        state_simp_rules, stored.pointer, stored.payload, NatOperand.pointer, NatOperand.payload,
        first]
      simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

/-- The selector write is committed before the first comparison/child call. -/
theorem selector_initialized (s : ArmState) (selector : NatOperand)
    (stored : SelectorAt s selector) (bound : (r (.GPR 20#5) s).toNat + 1 ≤ 2 ^ 64) :
    UInt8.ofBitVec (read_mem_bytes 1 (r (.GPR 20#5) s)
      (block (selectorOps selector) s)) = UInt8.ofNat selector.value := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (selector_memory s selector stored)),
    BoolCodec.read_mem_bytes_write_mem_bytes_same _ 1 _ _ bound]
  exact lowWord_byte selector

theorem selector_frame (s : ArmState) (selector : NatOperand)
    (stored : SelectorAt s selector) (bound : (r (.GPR 20#5) s).toNat + 1 ≤ 2 ^ 64) :
    Delimited.MemoryFrame [((r (.GPR 20#5) s).toNat, 1)]
      s (block (selectorOps selector) s) := by
  intro address outside
  rw [selector_memory s selector stored]
  exact BoolCodec.write_mem_bytes_frame _ _ 1 _ address bound
    (outside ((r (.GPR 20#5) s).toNat, 1) (by simp))

end SszArm.Codec.Emit.Union
