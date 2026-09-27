import SszArm.NatAddReturnStatus

namespace SszArm.NatAdd

open BoolCodec
open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Reservation failure and checked-count overflow use distinct real store
orders, but the same complete private arithmetic error layout. -/
inductive ErrorPath where
  | scratch | sizeOverflow

def ErrorPath.start : ErrorPath → Nat
  | .scratch => 1248
  | .sizeOverflow => 2212

def ErrorPath.ops : ErrorPath → List Op
  | .scratch =>
      [.p1248, .p1252, .p1256, .p1260, .p1264, .p1268, .p1272, .p1276,
       .p1280, .p1284, .p1288, .p1292, .p1296, .p1300, .p1304, .p1308,
       .p1312, .p1316, .p1320, .p1324, .p1328, .p1332, .p1336, .p1340,
       .p1344, .p1348, .p1352, .p1356, .p1360, .p1364, .p1368, .p1372,
       .p1376, .p1380, .p1384, .p1388, .p1392, .p1396, .p1400, .p1404,
       .p1408, .p1412, .p1416, .p1420, .p1424, .p1428, .p1432, .p1436,
       .p1440, .p1444]
  | .sizeOverflow =>
      [.p2212, .p2216, .p2220, .p2224, .p2228, .p2232, .p2236, .p2240,
       .p2244, .p2248, .p2252, .p2256, .p2260, .p2264, .p2268, .p2272,
       .p2276, .p2280, .p2284, .p2288, .p2292, .p2296, .p2300, .p2304,
       .p2308, .p2312, .p2316, .p2320, .p2324, .p2328, .p2332, .p2336,
       .p2340, .p2344, .p2348, .p2352, .p2356, .p2360, .p2364, .p2368,
       .p2372, .p2376, .p2380, .p2384, .p2388, .p2392, .p2396, .p2400,
       .p2404, .p2408]

def errorResult (path : ErrorPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base path.ops s

macro "natadd_error_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [errorResult, ErrorPath.ops, block, List.foldl_cons, List.foldl_nil,
     Op.effect, put, next, state_simp_rules, ArmState.mem_w_eq_mem,
     BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat,
     Nat.reduceAdd, BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases path <;> natadd_error_expand
  · simpa only [errorResult, block_error] using he
  · cases path <;> natadd_error_expand
  · intro reg low high
    have h8 : reg ≠ 8#5 := by bv_omega
    have h9 : reg ≠ 9#5 := by bv_omega
    have h10 : reg ≠ 10#5 := by bv_omega
    have h31 : reg ≠ 31#5 := by bv_omega
    cases path <;>
      simp [errorResult, ErrorPath.ops, block, Op.effect, put, next,
        state_simp_rules, h8, h9, h10, h31]
  · intro reg low high
    cases path <;>
      simp [errorResult, ErrorPath.ops, block, Op.effect, put, next, state_simp_rules]

/-- No arena byte is added on either resource-error return path. -/
theorem error_frame (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (localWrites s) s (errorResult path base s) := by
  obtain ⟨stack, output, separate⟩ := owned
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  cases path <;> natadd_error_expand <;> natadd_return_reads <;>
    simp (disch := natadd_return_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

/-- Pointer one, all seven remaining u64 fields zero, and exactly a u32 32768
at output+64. No fourth status byte is omitted or extra padding overwritten. -/
theorem error_image (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (errorResult path base s))
      (r (.GPR 0#5) s).toNat (.error .scratchExhausted) := by
  obtain ⟨stack, output, separate⟩ := owned
  change SszNative.NatArithmetic.errorAt _ _ .scratchExhausted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    cases path <;> natadd_error_expand <;> natadd_return_reads

/-- Repeated lowering spills remain exactly the original X9 and X10 words. -/
theorem error_spills (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (errorResult path base s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (errorResult path base s) = r (.GPR 10#5) s := by
  obtain ⟨stack, output, separate⟩ := owned
  constructor <;> cases path <;> natadd_error_expand <;> natadd_return_reads

theorem error_run_contract (path : ErrorPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start) (owned : ReturnOwned s) :
    run 50 s = errorResult path base s ∧
      Returned s (errorResult path base s) ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad (errorResult path base s))
        (r (.GPR 0#5) s).toNat (.error .scratchExhausted) ∧
      MemoryFrame (localWrites s) s (errorResult path base s) :=
  ⟨error_run path s base hc he ha hp, error_returned path s base he,
   error_image path s base owned, error_frame path s base owned⟩

end SszArm.NatAdd
