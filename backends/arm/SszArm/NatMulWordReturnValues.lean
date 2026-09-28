import SszArm.NatMulWordReturnStatus
import SszArm.NatAddReturnValues
import SszArm.NatMulWordReturnLower
import SszArm.NatMulStateFold

namespace SszArm.NatMulWord

open BoolCodec
open UintCodec (widthLoad)
open UintCodec.Tail (write_pair_words)
open Delimited (Span Protected MemoryFrame Returned)

def valueOps : StatusPath → List Op
  | .zero => [.p12, .p16, .p20, .p24, .p28, .p32, .p36, .p40, .p44, .p48, .p52]
  | .borrowed => [.p180]
  | .zeroBorrowed => [.p832, .p836, .p840, .p844, .p848, .p852, .p856, .p860, .p864, .p868, .p872]
  | .small => [.p1048, .p1052, .p1056, .p1060, .p1064, .p1068, .p1072, .p1076, .p1080, .p1084]
  | .wide => [.p1216]
  | .general => [.p1496]
  | .zeroGeneral => [.p1544, .p1548, .p1552, .p1556, .p1560, .p1564, .p1568, .p1572, .p1576, .p1580, .p1584]

def valueStart : StatusPath → Nat
  | .zero => 12 | .borrowed => 180 | .zeroBorrowed => 832 | .small => 1048
  | .wide => 1216 | .general => 1496 | .zeroGeneral => 1544

def valuePointer (path : StatusPath) (s : ArmState) : BitVec 64 :=
  match path with
  | .borrowed => r (.GPR 1#5) s
  | .wide => r (.GPR 10#5) s
  | .general => r (.GPR 9#5) s
  | _ => 0#64

def valuePayload (path : StatusPath) (s : ArmState) : BitVec 64 :=
  match path with
  | .borrowed => r (.GPR 2#5) s
  | .small | .wide | .general => r (.GPR 8#5) s
  | _ => 0#64

def valueBody (path : StatusPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base (valueOps path) s

def valueResult (path : StatusPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  statusResult path base (valueBody path base s)

/-- Bytes16..63 and the envelope tail68..71 are not success writes. -/
def valueWrites (s : ArmState) : List Span := NatAdd.valueWrites s

def valueAddPath : StatusPath → NatAdd.StatusPath
  | .borrowed => .left
  | .small => .zeroLarge
  | .general => .large
  | _ => .zeroRight

theorem value_body_eq_add (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (notWide : path ≠ .wide) :
    valueBody path base s = NatAdd.valueBody (valueAddPath path) base s := by
  have effects : (valueOps path).map (Op.effect base) =
      (NatAdd.valueOps (valueAddPath path)).map (NatAdd.Op.effect base) := by
    cases path <;>
      simp only [valueOps, valueAddPath, NatAdd.valueOps, List.map_cons, List.map_nil,
        List.cons.injEq, and_true, true_and]
    case wide => exact (notWide rfl).elim
    all_goals repeat' apply And.intro
    all_goals
      funext t
      rfl
  simpa only [valueBody, block, NatAdd.valueBody, NatAdd.block, List.foldl_map] using
    congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects

def valueMemory (path : StatusPath) (s : ArmState) : ArmState :=
  match path with
  | .zero | .zeroBorrowed | .zeroGeneral => pairMemory s 0#64
  | .small => pairMemory s (r (.GPR 8#5) s)
  | _ => write_mem_bytes 16 (r (.GPR 0#5) s) (valuePayload path s ++ valuePointer path s) s

theorem zero_body_eq (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (zero : path = .zero ∨ path = .zeroBorrowed ∨ path = .zeroGeneral) :
    valueBody path base s = block base zeroPairOps s := by
  have effects : (valueOps path).map (Op.effect base) = zeroPairOps.map (Op.effect base) := by
    rcases zero with rfl | rfl | rfl <;>
      simp only [valueOps, zeroPairOps, PairKind.ops, PairKind.enterOps,
        PairKind.storeOps, PairKind.restoreOps, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    all_goals repeat' apply And.intro
    all_goals
      funext t
      rfl
  simpa only [valueBody, block, List.foldl_map] using
    congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects

theorem value_body_effect (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    valueBody path base s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * (valueOps path).length)) (valueMemory path s) := by
  cases path
  case zero =>
    rw [zero_body_eq .zero s base (Or.inl rfl)]
    exact zero_pair_effect s base owned
  case zeroBorrowed =>
    rw [zero_body_eq .zeroBorrowed s base (Or.inr (Or.inl rfl))]
    exact zero_pair_effect s base owned
  case zeroGeneral =>
    rw [zero_body_eq .zeroGeneral s base (Or.inr (Or.inr rfl))]
    exact zero_pair_effect s base owned
  case small => exact small_pair_effect s base owned
  all_goals rfl

theorem value_body_vectors (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (valueBody path base s) = r (.SFP reg) s := by
  exact NatMulStateFold.preserves (fun t op => Op.effect base op t)
    (fun t => r (.SFP reg) t) (valueOps path) s (by
      intro op _ t
      exact op.sfp base t reg)

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
  have advance : read_pc (valueBody path base s) =
      read_pc s + BitVec.ofNat 64 (4 * (valueOps path).length) := by
    exact NatMulStateFold.advancing (fun t op => Op.effect base op t) (valueOps path) s (by
      intro op member t
      cases path <;> simp only [valueOps, List.mem_cons, List.not_mem_nil, or_false] at member
      case zero =>
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Op.effect, put, next, state_simp_rules]
      case borrowed =>
        subst op; simp [Op.effect, next, state_simp_rules]
      case zeroBorrowed =>
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Op.effect, put, next, state_simp_rules]
      case small =>
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Op.effect, put, next, state_simp_rules]
      case wide =>
        subst op; simp [Op.effect, next, state_simp_rules]
      case general =>
        subst op; simp [Op.effect, next, state_simp_rules]
      case zeroGeneral =>
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Op.effect, put, next, state_simp_rules])
  rw [advance, hp]
  cases path <;> simp [valueStart, valueOps, StatusPath.start, BitVec.add_assoc]

@[simp] theorem value_body_out (path : StatusPath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 0#5) (valueBody path base s) = r (.GPR 0#5) s := by
  by_cases wide : path = .wide
  · subst path
    simp [valueBody, valueOps, block, Op.effect, next, state_simp_rules]
  · rw [value_body_eq_add path s base wide]
    exact NatAdd.value_body_out (valueAddPath path) s base

@[simp] theorem value_body_sp (path : StatusPath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (valueBody path base s) = r (.GPR 31#5) s := by
  by_cases wide : path = .wide
  · subst path
    simp [valueBody, valueOps, block, Op.effect, next, state_simp_rules]
  · rw [value_body_eq_add path s base wide]
    exact NatAdd.value_body_sp (valueAddPath path) s base

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

theorem value_body_registers (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) :
    r (.GPR reg) (valueBody path base s) = r (.GPR reg) s := by
  rw [value_body_effect path s base owned,
    r_of_w_different (show StateField.GPR reg ≠ .PC by intro h; cases h)]
  cases path <;> simp only [valueMemory, pairMemory, NatFromU128.scratchPair, r_of_write_mem_bytes]

theorem value_registers (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (reg : BitVec 5) :
    r (.GPR reg) (valueResult path base s) = r (.GPR reg) s := by
  unfold valueResult
  rw [status_registers path _ base (value_body_owned path s base owned)]
  exact value_body_registers path s base owned reg

theorem value_returned (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (owned : ReturnOwned s) : Returned s (valueResult path base s) := by
  have returned := status_returned path (valueBody path base s) base
    (by simpa only [valueBody, block_error] using he)
  refine ⟨?_, returned.error, value_registers path s base owned _, ?_, ?_⟩
  · simpa only [valueResult, value_body_registers path s base owned] using returned.pc
  · intro reg _ _
    exact value_registers path s base owned reg
  · intro reg low high
    simpa only [valueResult] using (returned.vectors reg low high).trans
      (congrArg (fun x : BitVec 128 => x.setWidth 64) (value_body_vectors path s base reg))

theorem value_body_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (valueWrites s) s (valueBody path base s) := by
  intro a outside
  rw [value_body_effect path s base owned, ArmState.mem_w_eq_mem]
  obtain ⟨stack, output, separate⟩ := owned
  have descriptor := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [valueWrites, NatAdd.valueWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [valueWrites, NatAdd.valueWrites])
  cases path <;>
    simp (disch := natadd_return_side) [valueMemory, pairMemory, NatFromU128.scratchPair,
      write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem value_frame (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) : MemoryFrame (valueWrites s) s (valueResult path base s) := by
  apply (value_body_frame path s base owned).trans
  intro a outside
  apply status_frame path (valueBody path base s) base (value_body_owned path s base owned) a
  intro span member
  apply outside span
  simp only [statusWrites, NatAdd.statusWrites, value_body_out, value_body_sp,
    List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [valueWrites, NatAdd.valueWrites, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr member

theorem value_body_header_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    widthLoad (valueBody path base s) (r (.GPR 0#5) s).toNat 8 = some (valuePointer path s).toNat ∧
    widthLoad (valueBody path base s) ((r (.GPR 0#5) s).toNat + 8) 8 = some (valuePayload path s).toNat := by
  rw [value_body_effect path s base owned]
  obtain ⟨stack, output, separate⟩ := owned
  constructor
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    cases path <;> simp only [valueMemory, valuePointer, valuePayload,
      pairMemory, NatFromU128.scratchPair] <;>
      (try simp (disch := natadd_return_side) only [write_pair_words]) <;> natadd_return_reads

theorem value_header_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    widthLoad (valueResult path base s) (r (.GPR 0#5) s).toNat 8 = some (valuePointer path s).toNat ∧
    widthLoad (valueResult path base s) ((r (.GPR 0#5) s).toNat + 8) 8 = some (valuePayload path s).toNat := by
  have frame := status_frame path (valueBody path base s) base (value_body_owned path s base owned)
  have header := status_header_owned (valueBody path base s) (value_body_owned path s base owned)
  simp only [value_body_out] at header
  have bound := owned.output
  have image := value_body_header_image path s base owned
  constructor
  · exact (frame.load _ 8 (by omega)
      (by simpa only [Nat.add_zero] using header.subspan 0 8 (by decide))).trans image.1
  · exact (frame.load _ 8 (by omega) (header.subspan 8 8 (by decide))).trans image.2

theorem value_success_image (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (operand : SszNative.NatOperand)
    (pointer : valuePointer path s = operand.pointer)
    (payload : valuePayload path s = operand.payload)
    (input : operand.At (widthLoad s)) (borrowed : NatAdd.OperandOwned (valueWrites s) operand) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (valueResult path base s))
      (r (.GPR 0#5) s).toNat (.ok operand) := by
  have header := value_header_image path s base owned
  refine ⟨⟨?_, ?_, NatAdd.operand_at_preserved (value_frame path s base owned) operand input borrowed⟩, ?_⟩
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

theorem value_spills (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (valueResult path base s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (valueResult path base s) = r (.GPR 10#5) s := by
  simpa only [valueResult, value_body_registers path s base owned] using
    status_spills path (valueBody path base s) base (value_body_owned path s base owned)

theorem value_run_contract (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (valueStart path))
    (owned : ReturnOwned s) (operand : SszNative.NatOperand)
    (pointer : valuePointer path s = operand.pointer)
    (payload : valuePayload path s = operand.payload)
    (input : operand.At (widthLoad s)) (borrowed : NatAdd.OperandOwned (valueWrites s) operand) :
    run ((valueOps path).length + 11) s = valueResult path base s ∧
      Returned s (valueResult path base s) ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad (valueResult path base s))
        (r (.GPR 0#5) s).toNat (.ok operand) ∧
      MemoryFrame (valueWrites s) s (valueResult path base s) :=
  ⟨value_run path s base hc he ha hp, value_returned path s base he owned,
   value_success_image path s base owned operand pointer payload input borrowed,
   value_frame path s base owned⟩

theorem value_padding (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (owned : ReturnOwned s) (a : BitVec 64)
    (padding : ((r (.GPR 0#5) s).toNat + 16 ≤ a.toNat ∧ a.toNat < (r (.GPR 0#5) s).toNat + 64) ∨
      ((r (.GPR 0#5) s).toNat + 68 ≤ a.toNat ∧ a.toNat < (r (.GPR 0#5) s).toNat + 72)) :
    (valueResult path base s).mem a = s.mem a := by
  apply value_frame path s base owned a
  intro span member
  have stack := owned.stack
  have separate := owned.separate
  simp only [valueWrites, NatAdd.valueWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega

end SszArm.NatMulWord
