import SszArm.NatMulWordExec
import SszArm.NatMulWordContract
import SszArm.NatAddReturnStatus
import SszArm.NatFromU128Lower

namespace SszArm.NatMulWord

open BoolCodec
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

/-- Current physical output envelope and the actual transient lowering stack. -/
structure ReturnOwned (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 0#5) s).toNat + 72 ≤ 2^64
  separate : (r (.GPR 0#5) s).toNat + 72 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat

theorem ReturnOwned.add {s : ArmState} (owned : ReturnOwned s) : NatAdd.ReturnOwned s := by
  obtain ⟨stack, output, separate⟩ := owned
  exact ⟨stack, by omega, by omega⟩

theorem ReturnOwned.space {s : ArmState} (owned : ReturnOwned s) : NatFromU128.Space s :=
  ⟨owned.add.stack, owned.add.output, owned.add.separate⟩

theorem Owned.return_owned {s : ArmState} {operand : SszNative.NatOperand}
    {factor : BitVec 64} (owned : Owned s operand factor) : ReturnOwned s := by
  refine ⟨by have := owned.stackBound; omega, owned.outputBound, ?_⟩
  rcases owned.outputStack with empty | separate
  · omega
  · have apart := separate ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
    have stack := owned.stackBound
    simp only [Prod.fst, Prod.snd] at apart
    omega

inductive StatusPath where
  | zero | borrowed | zeroBorrowed | small | wide | general | zeroGeneral

def StatusPath.start : StatusPath → Nat
  | .zero => 56 | .borrowed => 184 | .zeroBorrowed => 876 | .small => 1088
  | .wide => 1220 | .general => 1500 | .zeroGeneral => 1588

def StatusPath.ops : StatusPath → List Op
  | .zero => [.p56, .p60, .p64, .p68, .p72, .p76, .p80, .p84, .p88, .p92, .p96]
  | .borrowed => [.p184, .p188, .p192, .p196, .p200, .p204, .p208, .p212, .p216, .p220, .p224]
  | .zeroBorrowed => [.p876, .p880, .p884, .p888, .p892, .p896, .p900, .p904, .p908, .p912, .p916]
  | .small => [.p1088, .p1092, .p1096, .p1100, .p1104, .p1108, .p1112, .p1116, .p1120, .p1124, .p1128]
  | .wide => [.p1220, .p1224, .p1228, .p1232, .p1236, .p1240, .p1244, .p1248, .p1252, .p1256, .p1260]
  | .general => [.p1500, .p1504, .p1508, .p1512, .p1516, .p1520, .p1524, .p1528, .p1532, .p1536, .p1540]
  | .zeroGeneral => [.p1588, .p1592, .p1596, .p1600, .p1604, .p1608, .p1612, .p1616, .p1620, .p1624, .p1628]

def statusResult (path : StatusPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base path.ops s

/-- Equality of the original instruction effects, not a substitute execution. -/
theorem status_eq_add (path : StatusPath) (s : ArmState) (base : BitVec 64) :
    statusResult path base s = NatAdd.statusResult .right base s := by
  have effects : path.ops.map (Op.effect base) =
      NatAdd.StatusPath.right.ops.map (NatAdd.Op.effect base) := by
    cases path <;>
      simp only [StatusPath.ops, NatAdd.StatusPath.ops, List.map_cons, List.map_nil,
        List.cons.injEq, and_true, true_and]
    all_goals repeat' apply And.intro
    all_goals
      funext t
      simp only [Op.effect, NatAdd.Op.effect, put, next, NatAdd.put, NatAdd.next,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  simpa only [statusResult, block, NatAdd.statusResult, NatAdd.block,
    List.foldl_map] using
    congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects

def statusWrites (s : ArmState) : List Span := NatAdd.statusWrites s

theorem status_run (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start) :
    run 11 s = statusResult path base s := by
  rw [show 11 = path.ops.length by cases path <;> rfl]
  apply block_run base path.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 path.start := hp
  cases path <;>
    simp [StatusPath.ops, StatusPath.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

theorem status_returned (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) : Returned s (statusResult path base s) := by
  rw [status_eq_add]
  exact NatAdd.status_returned .right s base he

theorem status_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (statusWrites s) s (statusResult path base s) := by
  rw [status_eq_add]
  exact NatAdd.status_frame .right s base owned.add

theorem status_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    widthLoad (statusResult path base s) ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 := by
  rw [status_eq_add]
  exact NatAdd.status_image .right s base owned.add

theorem status_spills (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (statusResult path base s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (statusResult path base s) = r (.GPR 10#5) s := by
  rw [status_eq_add]
  exact NatAdd.status_spills .right s base owned.add

/-- Every scalar register, including both lowering temporaries, is restored. -/
theorem status_registers (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) :
    r (.GPR reg) (statusResult path base s) = r (.GPR reg) s := by
  have eq : statusResult path base s =
      w .PC (r (.GPR 30#5) (NatFromU128.block base NatFromU128.LowerKind.smallStatus.ops s))
        (NatFromU128.block base NatFromU128.LowerKind.smallStatus.ops s) := by
    have effects : path.ops.map (Op.effect base) =
        NatFromU128.LowerKind.smallStatus.ops.map (NatFromU128.Op.effect base) ++
          [fun t => w .PC (r (.GPR 30#5) t) t] := by
      cases path <;>
        simp only [StatusPath.ops, NatFromU128.LowerKind.ops, List.map_cons,
          List.map_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
      all_goals repeat' apply And.intro
      all_goals
        funext t
        simp only [Op.effect, NatFromU128.Op.effect, put, next, NatFromU128.put, NatFromU128.next,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    have folded :=
      congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects
    simpa only [statusResult, block, NatFromU128.block, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_map] using folded
  rw [eq, r_of_w_different (show StateField.GPR reg ≠ .PC by intro h; cases h)]
  exact NatFromU128.lower_registers .smallStatus s base owned.space reg

theorem status_header_owned (s : ArmState) (owned : ReturnOwned s) :
    Protected (statusWrites s) (r (.GPR 0#5) s).toNat 16 :=
  NatAdd.status_header_owned s owned.add

end SszArm.NatMulWord
