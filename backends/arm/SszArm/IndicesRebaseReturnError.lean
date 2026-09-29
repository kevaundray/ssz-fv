import SszArm.IndicesLinkedRebase
import SszArm.NatAddReturnError
import SszArm.IndicesStorage

set_option autoImplicit false

namespace SszArm.Indices.RebaseReturn

open SszArm.NatAdd (Op)

inductive ErrorPath where
  | scratch | sizeOverflow

def ErrorPath.add : ErrorPath → NatAdd.ErrorPath
  | .scratch => .scratch
  | .sizeOverflow => .sizeOverflow

def ErrorPath.start : ErrorPath → Nat
  | .scratch => 748
  | .sizeOverflow => 104

def ErrorPath.bias (path : ErrorPath) (base : BitVec 64) : BitVec 64 :=
  base + BitVec.ofNat 64 path.start - BitVec.ofNat 64 path.add.start

def errorResult (path : ErrorPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  NatAdd.errorResult path.add (path.bias base) s

private theorem error_step (path : ErrorPath) (op : Op)
    (member : op ∈ path.add.ops) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some op.row.2) :
    stepi s = op.effect base s := by
  cases path <;>
    simp only [ErrorPath.add, NatAdd.ErrorPath.ops, List.mem_cons,
      List.not_mem_nil, or_false] at member
  all_goals
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, NatAdd.put, NatAdd.next, exec_inst, state_simp_rules,
        bitvec_rules, minimal_theory, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

private theorem mapped_code (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) :
    ∀ op ∈ path.add.ops,
      s.program.find? (path.bias base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
  intro op member
  cases path <;>
    simp only [ErrorPath.add, NatAdd.ErrorPath.ops, List.mem_cons,
      List.not_mem_nil, or_false] at member
  all_goals
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    simp only [ErrorPath.bias, ErrorPath.start, ErrorPath.add, NatAdd.ErrorPath.start,
      Op.row, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    apply code
    decide

private theorem mapped_run (path : ErrorPath) (ops : List Op) (s : ArmState)
    (base : BitVec 64) (members : ∀ op ∈ ops, op ∈ path.add.ops)
    (code : ∀ op ∈ ops, s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : NatAdd.Follows base ops s) :
    run ops.length s = NatAdd.block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = NatAdd.block base ops (op.effect base s)
    rw [run, error_step path op (members _ List.mem_cons_self) s base error aligned
      (by rw [follows.1]; exact code _ List.mem_cons_self)]
    apply ih _ (fun child h => members child (List.mem_cons_of_mem _ h))
      (fun child h => by simpa only [Op.program] using code child (List.mem_cons_of_mem _ h))
      ((Op.error _ _ _).trans error) (Op.aligned _ _ _ aligned) follows.2

theorem error_run (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.start) :
    run 50 s = errorResult path base s := by
  change run 50 s = NatAdd.block (path.bias base) path.add.ops s
  rw [show 50 = path.add.ops.length by cases path <;> rfl]
  apply mapped_run path _ s _ (fun _ h => h) (mapped_code path s base code) error aligned
  have entry : r .PC s = path.bias base + BitVec.ofNat 64 path.add.start := by
    simpa [ErrorPath.bias, BitVec.sub_add_cancel] using pc
  cases path <;>
    simp [ErrorPath.add, NatAdd.ErrorPath.ops, NatAdd.ErrorPath.start,
      NatAdd.Follows, Op.row, Op.effect, NatAdd.put, NatAdd.next,
      state_simp_rules, entry, BitVec.add_assoc]

theorem error_returned (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) : Delimited.Returned s (errorResult path base s) :=
  NatAdd.error_returned path.add s (path.bias base) error

theorem error_frame (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : NatAdd.ReturnOwned s) :
    Delimited.MemoryFrame (NatAdd.localWrites s) s (errorResult path base s) :=
  NatAdd.error_frame path.add s (path.bias base) owned

theorem error_image (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : NatAdd.ReturnOwned s) :
    SszNative.NatArithmetic.AddResultAt (UintCodec.widthLoad (errorResult path base s))
      (r (.GPR 0#5) s).toNat (.error .scratchExhausted) :=
  NatAdd.error_image path.add s (path.bias base) owned

theorem error_preserves (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : NatAdd.ReturnOwned s) (image : Codec.Storage.Image)
    (readonly : image.Owned (NatAdd.localWrites s) s) :
    image.Owned (NatAdd.localWrites s) (errorResult path base s) :=
  Codec.Storage.Image.preserved _ (error_frame path s base owned) readonly

end SszArm.Indices.RebaseReturn
