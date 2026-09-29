import SszArm.IndicesLinkedPrefixEqual
import SszArm.NatToU128Scan

namespace SszArm.Indices.PrefixEqual.Load

/-- The two guarded low-limb loads use identical lowering slots. Their source
pointers already name one word past the word being observed. -/
inductive Side where
  | left | right
  deriving DecidableEq

def Side.offset : Side → Nat
  | .left => 780
  | .right => 928

def Side.source : Side → BitVec 5
  | .left => 2
  | .right => 18

def Side.target : Side → BitVec 5
  | .left => 3
  | .right => 7

inductive Op where
  | lower | save | address | predecessor | load | restore | raise
  deriving DecidableEq

def Op.offset : Op → Nat
  | .lower => 0
  | .save => 4
  | .address => 8
  | .predecessor => 12
  | .load => 16
  | .restore => 20
  | .raise => 24

def Op.word (side : Side) : Op → BitVec 32
  | .lower => 0xd10043ff
  | .save => 0xf90003e9
  | .address => match side with | .left => 0x91000049 | .right => 0x91000249
  | .predecessor => 0xd1002129
  | .load => match side with | .left => 0xf9400123 | .right => 0xf9400127
  | .restore => 0xf94003e9
  | .raise => 0x910043ff

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (side : Side) : Op → ArmState → ArmState
  | .lower, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .save, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .address, s => put 9 (r (.GPR side.source) s) s
  | .predecessor, s => put 9 (r (.GPR 9#5) s - 8#64) s
  | .load, s => put side.target (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .restore, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .raise, s => put 31 (r (.GPR 31#5) s + 16#64) s

theorem step (side : Side) (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (side.offset + op.offset)) :
    stepi s = op.effect side s := by
  have fetched := Linked.PrefixEqual.chunk3_codeAt code
    (side.offset + op.offset, op.word side) (by cases side <;> cases op <;> decide)
  cases side <;> cases op
  all_goals
    simp only [Side.offset, Op.offset, Op.word, Nat.reduceAdd] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, Side.source, Side.target, put, next, exec_inst, state_simp_rules,
        bitvec_rules, minimal_theory, aligned, BitVec.sub_eq_add_neg]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem Op.program (side : Side) (op : Op) (s : ArmState) :
    (op.effect side s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

@[simp] theorem Op.error (side : Side) (op : Op) (s : ArmState) :
    read_err (op.effect side s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

theorem Op.aligned (side : Side) (op : Op) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect side s) := by
  cases side <;> cases op <;>
    simp [Op.effect, Side.target, put, next, state_simp_rules, aligned]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

def block (side : Side) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect side t) s

def Follows (side : Side) (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = base + BitVec.ofNat 64 (side.offset + op.offset) ∧
      Follows side base rest (op.effect side s)

theorem block_run (side : Side) (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows side base ops s) :
    run ops.length s = block side ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      change run (rest.length + 1) s = block side rest (op.effect side s)
      rw [run, step side op s base code error aligned follows.1]
      exact ih _ (Codec.Linked.WordsAt.preserve code (op.program side s))
        ((op.error side s).trans error) (op.aligned side s aligned) follows.2

def ops : List Op := [.lower, .save, .address, .predecessor, .load, .restore, .raise]

def loaded (side : Side) (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (side.offset + 28))
    (w (.GPR side.target) limb (NatCompare.saved s 9#5))

theorem load_run (side : Side) (s : ArmState) (base limb : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 side.offset)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (observed : read_mem_bytes 8 (r (.GPR side.source) s - 8#64)
      (NatCompare.saved s 9#5) = limb) :
    run 7 s = loaded side s base limb := by
  have storeBound : (r (.GPR 31#5) s - 16#64).toNat + 8 ≤ 2^64 := by
    have bound := (r (.GPR 31#5) s).isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ storeBound
  have follows : Follows side base ops s := by
    cases side <;> simp [ops, Follows, Op.offset, Op.effect, Side.offset, Side.target,
      put, next, state_simp_rules, pc, BitVec.add_assoc]
  rw [show 7 = ops.length by rfl, block_run side ops s base code error aligned follows]
  simp only [NatCompare.saved] at observed restored
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
        cases side <;>
          by_cases destination : reg = 3#5 <;> by_cases otherDestination : reg = 7#5 <;>
          by_cases temporary : reg = 9#5 <;> by_cases sp : reg = 31#5 <;>
          (try subst reg) <;>
          simp_all (config := {decide := true, instances := true})
            [loaded, block, ops, Op.effect, Side.offset, Side.source, Side.target,
              put, next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
              BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
        cases side <;> simp_all (config := {decide := true, instances := true})
          [loaded, block, ops, Op.effect, Side.offset, Side.source, Side.target,
            put, next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg =>
        simp [loaded, block, ops, Op.effect, put, next, NatCompare.saved, state_simp_rules]
    | FLAG flag =>
        simp [loaded, block, ops, Op.effect, put, next, NatCompare.saved, state_simp_rules]
    | ERR =>
        simp [loaded, block, ops, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  · simp [loaded, block, ops, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  · intro n address
    cases side <;> simp [loaded, block, ops, Op.effect, Side.source, Side.target,
      put, next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

end SszArm.Indices.PrefixEqual.Load
