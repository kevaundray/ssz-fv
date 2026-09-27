import SszArm.NatAddExec
import SszArm.NatAddContract

namespace SszArm.NatAdd

open BoolCodec
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical geometry needed by the leaf's lowered output stores. -/
structure ReturnOwned (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  separate : (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat

theorem Owned.return_owned {s : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) : ReturnOwned s := by
  refine ⟨owned.stackBound, owned.outputBound, ?_⟩
  rcases owned.outputStack with empty | separate
  · omega
  · have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
    have stack := owned.stackBound
    simp only [Prod.fst, Prod.snd] at apart
    omega

/-- Every instance of the same lowered 32-bit zero-status store and actual RET. -/
inductive StatusPath where
  | right | left | zeroRight | zeroLeft | small | wide | large | zeroLarge

def StatusPath.start : StatusPath → Nat
  | .right => 496 | .left => 660 | .zeroRight => 748 | .zeroLeft => 836
  | .small => 1044 | .wide => 1204 | .large => 2084 | .zeroLarge => 2168

def StatusPath.ops : StatusPath → List Op
  | .right => [.p496, .p500, .p504, .p508, .p512, .p516, .p520, .p524, .p528, .p532, .p536]
  | .left => [.p660, .p664, .p668, .p672, .p676, .p680, .p684, .p688, .p692, .p696, .p700]
  | .zeroRight => [.p748, .p752, .p756, .p760, .p764, .p768, .p772, .p776, .p780, .p784, .p788]
  | .zeroLeft => [.p836, .p840, .p844, .p848, .p852, .p856, .p860, .p864, .p868, .p872, .p876]
  | .small => [.p1044, .p1048, .p1052, .p1056, .p1060, .p1064, .p1068, .p1072, .p1076, .p1080, .p1084]
  | .wide => [.p1204, .p1208, .p1212, .p1216, .p1220, .p1224, .p1228, .p1232, .p1236, .p1240, .p1244]
  | .large => [.p2084, .p2088, .p2092, .p2096, .p2100, .p2104, .p2108, .p2112, .p2116, .p2120, .p2124]
  | .zeroLarge => [.p2168, .p2172, .p2176, .p2180, .p2184, .p2188, .p2192, .p2196, .p2200, .p2204, .p2208]

def statusResult (path : StatusPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base path.ops s

/-- In particular the success tail does not write the result's padding. -/
def statusWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat + 64, 4), ((r (.GPR 31#5) s).toNat - 16, 16)]

macro "natadd_return_side" : tactic => `(tactic|
  first | assumption | omega | bv_omega)

macro "natadd_status_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [statusResult, StatusPath.ops, block, List.foldl_cons, List.foldl_nil,
     Op.effect, put, next, state_simp_rules, ArmState.mem_w_eq_mem,
     BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat,
     Nat.reduceAdd, BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

macro "natadd_return_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := natadd_return_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases path <;> natadd_status_expand
  · simpa only [statusResult, block_error] using he
  · cases path <;> natadd_status_expand
  · intro reg low high
    have h9 : reg ≠ 9#5 := by bv_omega
    have h10 : reg ≠ 10#5 := by bv_omega
    have h31 : reg ≠ 31#5 := by bv_omega
    cases path <;>
      simp [statusResult, StatusPath.ops, block, Op.effect, put, next,
        state_simp_rules, h9, h10, h31]
  · intro reg low high
    cases path <;>
      simp [statusResult, StatusPath.ops, block, Op.effect, put, next, state_simp_rules]

theorem status_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (statusWrites s) s (statusResult path base s) := by
  obtain ⟨stack, output, separate⟩ := owned
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [statusWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [statusWrites])
  cases path <;> natadd_status_expand <;> natadd_return_reads <;>
    simp (disch := natadd_return_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem status_local_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (localWrites s) s (statusResult path base s) := by
  intro a outside
  apply status_frame path s base owned a
  intro span member
  simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
    simp only [Prod.fst, Prod.snd] at *
    omega
  · exact outside _ (by simp [localWrites])

theorem status_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    widthLoad (statusResult path base s) ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 := by
  obtain ⟨stack, output, separate⟩ := owned
  simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  cases path <;> natadd_status_expand <;> natadd_return_reads

/-- Both persistent spill words are accounted for; restoring SP does not erase them. -/
theorem status_spills (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (statusResult path base s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (statusResult path base s) = r (.GPR 10#5) s := by
  obtain ⟨stack, output, separate⟩ := owned
  constructor <;> cases path <;> natadd_status_expand <;> natadd_return_reads

theorem status_header_owned (s : ArmState) (owned : ReturnOwned s) :
    Protected (statusWrites s) (r (.GPR 0#5) s).toNat 16 := by
  right
  intro span member
  simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain ⟨stack, output, separate⟩ := owned
  rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega

/-- Callers supply the already-proved pointer/payload stores. The actual tail
preserves those stores and the exact borrowed limbs while writing status zero. -/
theorem status_success_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (operand : SszNative.NatOperand)
    (stored : SszNative.NatArithmetic.operandAt (widthLoad s) (r (.GPR 0#5) s).toNat operand)
    (borrowed : OperandOwned (statusWrites s) operand) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (statusResult path base s))
      (r (.GPR 0#5) s).toNat (.ok operand) := by
  have frame := status_frame path s base owned
  have header := status_header_owned s owned
  have bound := owned.output
  refine ⟨⟨?_, ?_, operand_at_preserved frame operand stored.2.2 borrowed⟩,
    status_image path s base owned⟩
  · rw [frame.load _ 8 (by omega) (by simpa only [Nat.add_zero] using header.subspan 0 8 (by decide))]
    exact stored.1
  · rw [frame.load _ 8 (by omega) (header.subspan 8 8 (by decide))]
    exact stored.2.1

theorem status_small_image (path : StatusPath) (s : ArmState) (base word : BitVec 64)
    (owned : ReturnOwned s)
    (pointer : widthLoad s (r (.GPR 0#5) s).toNat 8 = some 0)
    (payload : widthLoad s ((r (.GPR 0#5) s).toNat + 8) 8 = some word.toNat) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (statusResult path base s))
      (r (.GPR 0#5) s).toNat (.ok (.small word)) :=
  status_success_image path s base owned (.small word) ⟨pointer, payload, trivial⟩ trivial

end SszArm.NatAdd
