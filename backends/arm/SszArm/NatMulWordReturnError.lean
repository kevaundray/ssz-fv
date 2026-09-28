import SszArm.NatMulWordReturnStatus
import SszArm.NatAddReturnError
import SszArm.NatMulWordReturnErrorRestore

namespace SszArm.NatMulWord

open BoolCodec
open UintCodec (widthLoad)
open Delimited (Span MemoryFrame Returned)

inductive ErrorPath where
  | scratch | sizeOverflow

def ErrorPath.start : ErrorPath → Nat
  | .scratch => 1264 | .sizeOverflow => 1632

def ErrorPath.ops : ErrorPath → List Op
  | .scratch =>
      [.p1264, .p1268, .p1272, .p1276, .p1280, .p1284, .p1288, .p1292,
       .p1296, .p1300, .p1304, .p1308, .p1312, .p1316, .p1320, .p1324,
       .p1328, .p1332, .p1336, .p1340, .p1344, .p1348, .p1352, .p1356,
       .p1360, .p1364, .p1368, .p1372, .p1376, .p1380, .p1384, .p1388,
       .p1392, .p1396, .p1400, .p1404, .p1408, .p1412, .p1416, .p1420,
       .p1424, .p1428, .p1432, .p1436, .p1440, .p1444, .p1448, .p1452,
       .p1456, .p1460]
  | .sizeOverflow =>
      [.p1632, .p1636, .p1640, .p1644, .p1648, .p1652, .p1656, .p1660,
       .p1664, .p1668, .p1672, .p1676, .p1680, .p1684, .p1688, .p1692,
       .p1696, .p1700, .p1704, .p1708, .p1712, .p1716, .p1720, .p1724,
       .p1728, .p1732, .p1736, .p1740, .p1744, .p1748, .p1752, .p1756,
       .p1760, .p1764, .p1768, .p1772, .p1776, .p1780, .p1784, .p1788,
       .p1792, .p1796, .p1800, .p1804, .p1808, .p1812, .p1816, .p1820,
       .p1824, .p1828]

def ErrorPath.add : ErrorPath → NatAdd.ErrorPath
  | .scratch => .scratch | .sizeOverflow => .sizeOverflow

def errorResult (path : ErrorPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base path.ops s

/-- Both original store orders match the already-proved lowering sequences. -/
theorem error_eq_add (path : ErrorPath) (s : ArmState) (base : BitVec 64) :
    errorResult path base s = NatAdd.errorResult path.add base s := by
  have effects : path.ops.map (Op.effect base) =
      path.add.ops.map (NatAdd.Op.effect base) := by
    cases path <;>
      simp only [ErrorPath.ops, ErrorPath.add, NatAdd.ErrorPath.ops,
        List.map_cons, List.map_nil, List.cons.injEq, and_true]
    all_goals repeat' apply And.intro
    all_goals
      funext t
      simp only [Op.effect, NatAdd.Op.effect, put, next, NatAdd.put, NatAdd.next,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  simpa only [errorResult, block, NatAdd.errorResult, NatAdd.block,
    List.foldl_map] using
    congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects

def errorWrites (s : ArmState) : List Span := NatAdd.localWrites s

theorem error_run (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start) :
    run 50 s = errorResult path base s := by
  rw [show 50 = path.ops.length by cases path <;> rfl]
  apply block_run base path.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 path.start := hp
  cases path <;>
    simp [ErrorPath.ops, ErrorPath.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

theorem error_returned (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) : Returned s (errorResult path base s) := by
  rw [error_eq_add]
  exact NatAdd.error_returned path.add s base he

/-- Only output0..67 and the real 16-byte spill slot are changed. -/
theorem error_frame (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (errorWrites s) s (errorResult path base s) := by
  rw [error_eq_add]
  exact NatAdd.error_frame path.add s base owned.add

theorem error_image (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (errorResult path base s))
      (r (.GPR 0#5) s).toNat (.error .scratchExhausted) := by
  rw [error_eq_add]
  exact NatAdd.error_image path.add s base owned.add

theorem error_spills (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (errorResult path base s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (errorResult path base s) = r (.GPR 10#5) s := by
  rw [error_eq_add]
  exact NatAdd.error_spills path.add s base owned.add

/-- X8 is the sole scalar clobber; lowering restores X9/X10 from actual spills. -/
theorem error_registers (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) (h8 : reg ≠ 8#5) :
    r (.GPR reg) (errorResult path base s) = r (.GPR reg) s := by
  rw [error_eq_add]
  exact add_error_registers path.add s base owned reg h8

theorem error_padding (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (a : BitVec 64)
    (low : (r (.GPR 0#5) s).toNat + 68 ≤ a.toNat)
    (high : a.toNat < (r (.GPR 0#5) s).toNat + 72) :
    (errorResult path base s).mem a = s.mem a := by
  apply error_frame path s base owned a
  intro span member
  have stack := owned.stack
  have separate := owned.separate
  simp only [errorWrites, NatAdd.localWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> omega

theorem error_run_contract (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start) (owned : ReturnOwned s) :
    run 50 s = errorResult path base s ∧
      Returned s (errorResult path base s) ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad (errorResult path base s))
        (r (.GPR 0#5) s).toNat (.error .scratchExhausted) ∧
      MemoryFrame (errorWrites s) s (errorResult path base s) :=
  ⟨error_run path s base hc he ha hp, error_returned path s base he,
   error_image path s base owned, error_frame path s base owned⟩

end SszArm.NatMulWord
