import SszArm.NatMulReturnFrame

namespace SszArm.NatMul

open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

inductive ReturnErrorPath where
  | scratch | sizeOverflow

def ReturnErrorPath.start : ReturnErrorPath → Nat
  | .scratch => 1076 | .sizeOverflow => 1344

def ReturnErrorPath.prefix : ReturnErrorPath → List Op
  | .scratch =>
    [.p1076, .p1080, .p1084, .p1088, .p1092, .p1096, .p1100, .p1104,
     .p1108, .p1112, .p1116, .p1120, .p1124, .p1128, .p1132, .p1136,
     .p1140, .p1144, .p1148, .p1152, .p1156, .p1160, .p1164, .p1168,
     .p1172, .p1176, .p1180, .p1184, .p1188, .p1192, .p1196, .p1200,
     .p1204, .p1208, .p1212, .p1216, .p1220, .p1224, .p1228, .p1232,
     .p1236, .p1240, .p1244, .p1248, .p1252, .p1256, .p1260, .p1264, .p1268]
  | .sizeOverflow =>
    [.p1344, .p1348, .p1352, .p1356, .p1360, .p1364, .p1368, .p1372,
     .p1376, .p1380, .p1384, .p1388, .p1392, .p1396, .p1400, .p1404,
     .p1408, .p1412, .p1416, .p1420, .p1424, .p1428, .p1432, .p1436,
     .p1440, .p1444, .p1448, .p1452, .p1456, .p1460, .p1464, .p1468,
     .p1472, .p1476, .p1480, .p1484, .p1488, .p1492, .p1496, .p1500,
     .p1504, .p1508, .p1512, .p1516, .p1520, .p1524, .p1528]

def ReturnErrorPath.tail : ReturnErrorPath → List Op
  | .scratch => [.p1272]
  | .sizeOverflow => [.p1532, .p1264, .p1268, .p1272]

def ReturnErrorPath.ops (path : ReturnErrorPath) : List Op := path.prefix ++ path.tail

def ReturnErrorPath.word : ReturnErrorPath → NatMulWord.ErrorPath
  | .scratch => .scratch | .sizeOverflow => .sizeOverflow

private def ReturnErrorPath.wordPrefix (path : ReturnErrorPath) : List NatMulWord.Op :=
  path.word.ops.take path.prefix.length

private def ReturnErrorPath.wordTail : ReturnErrorPath → List NatMulWord.Op
  | .scratch => [.p1460]
  | .sizeOverflow => [.p1820, .p1824, .p1828]

private theorem error_prefix_eq (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64) :
    block base path.prefix s = NatMulWord.block base path.wordPrefix s := by
  have effects : path.prefix.map (Op.effect base) =
      path.wordPrefix.map (NatMulWord.Op.effect base) := by
    cases path <;>
      simp only [ReturnErrorPath.prefix, ReturnErrorPath.wordPrefix, ReturnErrorPath.word,
        NatMulWord.ErrorPath.ops, List.length_cons, List.length_nil, List.take,
        List.map_cons, List.map_nil, Op.effect, NatMulWord.Op.effect,
        put, next, NatMulWord.put, NatMulWord.next]
  simpa only [block, NatMulWord.block, List.foldl_map] using
    congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects

def errorReturnBody (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64) : ArmState :=
  block base path.ops s

private theorem error_return_split (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64) :
    errorReturnBody path s base = block base path.tail (block base path.prefix s) := by
  simp only [errorReturnBody, ReturnErrorPath.ops, block, List.foldl_append]

theorem error_return_erased (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64) :
    w .PC 0#64 (errorReturnBody path s base) =
      w .PC 0#64 (NatMulWord.errorResult path.word base s) := by
  have split : path.word.ops = path.wordPrefix ++ path.wordTail := by cases path <;> rfl
  rw [error_return_split]
  rw [error_prefix_eq]
  simp only [NatMulWord.errorResult, split, NatMulWord.block, List.foldl_append]
  generalize NatMulWord.block base path.wordPrefix s = u
  cases path <;>
    simp [ReturnErrorPath.tail, ReturnErrorPath.wordTail, block, NatMulWord.block,
      Op.effect, NatMulWord.Op.effect, put, next, NatMulWord.put, NatMulWord.next,
      state_simp_rules, NatFromU128.store_field_write]

theorem error_return_body_run (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.start) :
    run path.ops.length s = errorReturnBody path s base := by
  apply block_run base path.ops s code error aligned
  have hpc : r .PC s = base + BitVec.ofNat 64 path.start := pc
  cases path <;>
    simp [ReturnErrorPath.ops, ReturnErrorPath.prefix, ReturnErrorPath.tail,
      ReturnErrorPath.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

theorem error_return_body_pc (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64) :
    read_pc (errorReturnBody path s base) = base + 348#64 := by
  rw [error_return_split]
  cases path <;> simp [ReturnErrorPath.tail, block, Op.effect, put, next, state_simp_rules]

theorem error_return_body_frame (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 0#5) s)) :
    MemoryFrame (returnErrorWrites s (r (.GPR 0#5) s)) s (errorReturnBody path s base) := by
  have memory := congrArg ArmState.mem (error_return_erased path s base)
  simp only [ArmState.mem_w_eq_mem] at memory
  intro a outside
  rw [memory]
  exact NatMulWord.error_frame path.word s base space.word a outside

theorem error_return_body_registers (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 0#5) s)) (reg : BitVec 5) (h8 : reg ≠ 8#5) :
    r (.GPR reg) (errorReturnBody path s base) = r (.GPR reg) s := by
  have same := congrArg (r (.GPR reg)) (error_return_erased path s base)
  simp only [state_simp_rules] at same
  exact same.trans (NatMulWord.error_registers path.word s base space.word reg h8)

/-- Both native error entrances write the shared scratchExhausted constructor:
payload one, seven zero u64s, and status 32768. -/
theorem error_return_body_image (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 0#5) s)) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (errorReturnBody path s base))
      (r (.GPR 0#5) s).toNat (.error .scratchExhausted) := by
  have memory := congrArg ArmState.mem (error_return_erased path s base)
  simp only [ArmState.mem_w_eq_mem] at memory
  have loads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  have observed : widthLoad (errorReturnBody path s base) =
      widthLoad (NatMulWord.errorResult path.word base s) := by
    funext a n; simp only [widthLoad, loads]
  rw [observed]
  exact NatMulWord.error_image path.word s base space.word

def errorReturned (path : ReturnErrorPath) (s : ArmState) (base : BitVec 64) : ArmState :=
  restored .return (errorReturnBody path s base) base

theorem error_return_run (path : ReturnErrorPath) (entry s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.start) (saved : Saved entry s)
    (space : ReturnSpace s (r (.GPR 0#5) s)) :
    run (path.ops.length + 7) s = errorReturned path s base ∧
      Returned entry (errorReturned path s base) ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad (errorReturned path s base))
        (r (.GPR 0#5) s).toNat (.error .scratchExhausted) ∧
      MemoryFrame (returnErrorWrites s (r (.GPR 0#5) s)) s (errorReturned path s base) := by
  have bodyFrame := error_return_body_frame path s base space
  have bodySaved := saved.return_frame space bodyFrame
    (error_return_body_registers path s base space 31#5 (by decide))
    (error_return_body_registers path s base space 29#5 (by decide))
    (by intro reg; cases path <;>
        simp [errorReturnBody, ReturnErrorPath.ops, ReturnErrorPath.prefix,
          ReturnErrorPath.tail, block, Op.effect, put, next, state_simp_rules])
  have bodyError : read_err (errorReturnBody path s base) = .None :=
    (block_error base path.ops s).trans error
  refine ⟨?_, return_restored entry _ base bodySaved bodyError, ?_, ?_⟩
  · rw [run_plus, error_return_body_run path s base code error aligned pc]
    exact restore_run .return _ base
      (by simpa only [errorReturnBody, CodeAt, block_program] using code) bodyError
      (block_aligned base path.ops s aligned) (error_return_body_pc path s base)
  · have loads := Memory.mem_eq_iff_read_mem_bytes_eq.mp
      (restore_memory .return (errorReturnBody path s base) base)
    have observed : widthLoad (errorReturned path s base) = widthLoad (errorReturnBody path s base) := by
      funext a n; simp only [errorReturned, widthLoad, loads]
    rw [observed]
    exact error_return_body_image path s base space
  · intro a outside
    exact (congrFun (restore_memory .return (errorReturnBody path s base) base) a).trans
      (bodyFrame a outside)

end SszArm.NatMul
