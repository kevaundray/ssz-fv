import SszArm.NatAddReturnStatus

namespace SszArm.NatAdd

open BoolCodec
open UintCodec (widthLoad)
open UintCodec.Tail (write_pair_words)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The actual pointer/payload stores immediately preceding each success tail. -/
def valueOps : StatusPath → List Op
  | .right => [.p492]
  | .left => [.p656]
  | .zeroRight => [.p704, .p708, .p712, .p716, .p720, .p724, .p728, .p732, .p736, .p740, .p744]
  | .zeroLeft => [.p792, .p796, .p800, .p804, .p808, .p812, .p816, .p820, .p824, .p828, .p832]
  | .small => [.p1004, .p1008, .p1012, .p1016, .p1020, .p1024, .p1028, .p1032, .p1036, .p1040]
  | .wide => [.p1196, .p1200]
  | .large => [.p2080]
  | .zeroLarge => [.p2128, .p2132, .p2136, .p2140, .p2144, .p2148, .p2152, .p2156, .p2160, .p2164]

def valueStart : StatusPath → Nat
  | .right => 492 | .left => 656 | .zeroRight => 704 | .zeroLeft => 792
  | .small => 1004 | .wide => 1196 | .large => 2080 | .zeroLarge => 2128

def valuePointer (path : StatusPath) (s : ArmState) : BitVec 64 :=
  match path with
  | .right => r (.GPR 3#5) s
  | .left => r (.GPR 1#5) s
  | .wide => r (.GPR 8#5) s
  | .large => r (.GPR 9#5) s
  | _ => 0#64

def valuePayload (path : StatusPath) (s : ArmState) : BitVec 64 :=
  match path with
  | .right => r (.GPR 4#5) s
  | .left => r (.GPR 2#5) s
  | .small => r (.GPR 9#5) s
  | .wide => 2#64
  | .large | .zeroLarge => r (.GPR 8#5) s
  | .zeroRight | .zeroLeft => 0#64

def valueBody (path : StatusPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base (valueOps path) s

def valueResult (path : StatusPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  statusResult path base (valueBody path base s)

/-- Success writes only its two descriptor words and u32 status, never bytes16..63. -/
def valueWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 16), ((r (.GPR 0#5) s).toNat + 64, 4),
   ((r (.GPR 31#5) s).toNat - 16, 16)]

macro "natadd_values_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [valueResult, statusResult, valueBody, valueOps, StatusPath.ops,
     block, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem value_body_run (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (valueStart path)) :
    run (valueOps path).length s = valueBody path base s := by
  apply block_run base (valueOps path) s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 (valueStart path) := hp
  cases path <;>
    simp [valueOps, valueStart, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

theorem value_body_pc (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + BitVec.ofNat 64 (valueStart path)) :
    read_pc (valueBody path base s) = base + BitVec.ofNat 64 path.start := by
  have hpc : r .PC s = base + BitVec.ofNat 64 (valueStart path) := hp
  cases path <;>
    simp [valueBody, valueOps, valueStart, StatusPath.start, block, Op.effect,
      put, next, state_simp_rules, hpc, BitVec.add_assoc]

@[simp] theorem value_body_out (path : StatusPath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 0#5) (valueBody path base s) = r (.GPR 0#5) s := by
  cases path <;> natadd_values_expand

@[simp] theorem value_body_sp (path : StatusPath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (valueBody path base s) = r (.GPR 31#5) s := by
  cases path <;> natadd_values_expand

theorem value_body_owned (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : ReturnOwned (valueBody path base s) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [value_body_sp] using owned.stack
  · simpa only [value_body_out] using owned.output
  · simpa only [value_body_out, value_body_sp] using owned.separate

theorem value_run (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (valueStart path)) :
    run ((valueOps path).length + 11) s = valueResult path base s := by
  rw [run_plus, value_body_run path s base hc he ha hp]
  exact status_run path (valueBody path base s) base
    (by simpa only [valueBody, CodeAt, block_program] using hc)
    (by simpa only [valueBody, block_error] using he)
    (block_aligned base (valueOps path) s ha) (value_body_pc path s base hp)

theorem value_returned (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) : Returned s (valueResult path base s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases path <;> natadd_values_expand
  · simpa only [valueResult, statusResult, valueBody, block_error] using he
  · cases path <;> natadd_values_expand
  · intro reg low high
    have h9 : reg ≠ 9#5 := by bv_omega
    have h10 : reg ≠ 10#5 := by bv_omega
    have h11 : reg ≠ 11#5 := by bv_omega
    have h31 : reg ≠ 31#5 := by bv_omega
    cases path <;>
      simp [valueResult, statusResult, valueBody, valueOps, StatusPath.ops,
        block, Op.effect, put, next, state_simp_rules, h9, h10, h11, h31]
  · intro reg low high
    cases path <;>
      simp [valueResult, statusResult, valueBody, valueOps, StatusPath.ops,
        block, Op.effect, put, next, state_simp_rules]

theorem value_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (valueWrites s) s (valueResult path base s) := by
  obtain ⟨stack, output, separate⟩ := owned
  intro a outside
  have descriptor := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [valueWrites])
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [valueWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [valueWrites])
  cases path <;> natadd_values_expand <;> natadd_return_reads <;>
    simp (disch := natadd_return_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem value_local_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (localWrites s) s (valueResult path base s) := by
  intro a outside
  apply value_frame path s base owned a
  intro span member
  simp only [valueWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
    simp only [Prod.fst, Prod.snd] at *
    omega
  · have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
    simp only [Prod.fst, Prod.snd] at *
    omega
  · exact outside _ (by simp [localWrites])

theorem value_header_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    widthLoad (valueResult path base s) (r (.GPR 0#5) s).toNat 8 = some (valuePointer path s).toNat ∧
    widthLoad (valueResult path base s) ((r (.GPR 0#5) s).toNat + 8) 8 = some (valuePayload path s).toNat := by
  obtain ⟨stack, output, separate⟩ := owned
  constructor
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    cases path <;> simp only [valuePointer, valuePayload] <;> natadd_values_expand <;>
      (try simp (disch := natadd_return_side) only [write_pair_words]) <;> natadd_return_reads

theorem value_padding (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (a : BitVec 64)
    (low : (r (.GPR 0#5) s).toNat + 16 ≤ a.toNat)
    (high : a.toNat < (r (.GPR 0#5) s).toNat + 64) :
    (valueResult path base s).mem a = s.mem a := by
  apply value_frame path s base owned a
  intro span member
  have stack := owned.stack
  have separate := owned.separate
  simp only [valueWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega

/-- Original or newly allocated limbs are protected only from the actual return
stores. Their exact representation is retained, including borrowed pointer identity. -/
theorem value_success_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (operand : SszNative.NatOperand)
    (pointer : valuePointer path s = operand.pointer)
    (payload : valuePayload path s = operand.payload)
    (input : operand.At (widthLoad s)) (borrowed : OperandOwned (valueWrites s) operand) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (valueResult path base s))
      (r (.GPR 0#5) s).toNat (.ok operand) := by
  have header := value_header_image path s base owned
  refine ⟨⟨?_, ?_, operand_at_preserved (value_frame path s base owned) operand input borrowed⟩, ?_⟩
  · simpa only [pointer] using header.1
  · simpa only [payload] using header.2
  · simpa only [valueResult, value_body_out] using
      status_image path (valueBody path base s) base (value_body_owned path s base owned)

theorem value_small_image (path : StatusPath) (s : ArmState) (base word : BitVec 64)
    (owned : ReturnOwned s) (pointer : valuePointer path s = 0#64)
    (payload : valuePayload path s = word) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (valueResult path base s))
      (r (.GPR 0#5) s).toNat (.ok (.small word)) :=
  value_success_image path s base owned (.small word) pointer payload trivial trivial

end SszArm.NatAdd
