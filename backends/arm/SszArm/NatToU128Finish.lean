import SszArm.NatToU128Memory
import SszArm.UintResultMemory

namespace SszArm.NatToU128

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The four actual return continuations, after all data-dependent branches. -/
inductive FinishPath where
  | none | small | one | two

def FinishPath.start : FinishPath → Nat
  | .none => 72 | .small => 196 | .one => 288 | .two => 136

def FinishPath.ops : FinishPath → List Op
  | .none => [.p72, .p76, .p80, .p84, .p88, .p92, .p96, .p100,
      .p104, .p108, .p112, .p116]
  | .small => [.p196, .p200, .p204, .p208, .p212, .p216, .p220, .p224,
      .p228, .p232, .p236, .p240, .p244, .p248, .p252, .p256,
      .p260, .p264, .p268, .p272, .p276, .p280, .p284]
  | .one => [.p288, .p292, .p296, .p300, .p304, .p308, .p312, .p316,
      .p320, .p324, .p328, .p332, .p336, .p340, .p344, .p348,
      .p352, .p356, .p360, .p364, .p368, .p372, .p376, .p380]
  | .two => [.p136, .p140, .p144, .p148, .p152, .p156, .p160, .p164,
      .p168, .p172, .p176, .p180, .p184, .p188, .p192]

def FinishPath.value : FinishPath → ArmState → Option (BitVec 128)
  | .none, _ => Option.none
  | .small, s => some ((r (.GPR 2#5) s).setWidth 128)
  | .one, s => some ((r (.GPR 8#5) s).setWidth 128)
  | .two, s => some (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ++ r (.GPR 8#5) s)

def FinishPath.bytes : FinishPath → Nat
  | .none => 16
  | _ => 32

def finishWrites (path : FinishPath) (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, path.bytes), ((r (.GPR 31#5) s).toNat - 16, 16)]

def finished (path : FinishPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base path.ops s

structure FinishSpace (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 0#5) s).toNat + 32 ≤ 2^64
  separate : (r (.GPR 0#5) s).toNat + 32 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat

theorem Owned.finishSpace {s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand) : FinishSpace s := by
  refine ⟨owned.stackBound, owned.outputBound, ?_⟩
  rcases owned.outputStack with empty | separate
  · omega
  · have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
    have stack := owned.stackBound
    omega

theorem FinishSpace.of_frame {s t : ArmState} (space : FinishSpace s)
    (frame : NatNarrow.Frame s t) : FinishSpace t := by
  have output := frame.registers 0#5 (by decide)
  exact ⟨by simpa only [frame.sp] using space.stack,
    by simpa only [output] using space.output,
    by simpa only [frame.sp, output] using space.separate⟩

macro "u128_finish_side" : tactic => `(tactic|
  first | assumption | omega | bv_omega)

macro "u128_finish_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [finished, FinishPath.ops, block, List.foldl_cons, List.foldl_nil,
     Op.effect, put, next, state_simp_rules, ArmState.mem_w_eq_mem,
     BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat,
     Nat.reduceAdd, BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

macro "u128_finish_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := u128_finish_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel, UintCodec.Tail.write_pair_words,
     BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint])

theorem finish_run (path : FinishPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start) :
    run path.ops.length s = finished path base s := by
  apply block_run base path.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 path.start := hp
  cases path <;>
    simp [FinishPath.ops, FinishPath.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

theorem block_error (base : BitVec 64) (ops : List Op) (s : ArmState) :
    read_err (block base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change read_err (block base ops (op.effect base s)) = read_err s
    rw [ih, Op.error]

theorem finish_returned (path : FinishPath) (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) : Returned s (finished path base s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases path <;> u128_finish_expand
  · simpa only [finished, block_error] using he
  · cases path <;> u128_finish_expand
  · intro reg low high
    have h2 : reg ≠ 2#5 := by bv_omega
    have h9 : reg ≠ 9#5 := by bv_omega
    have h10 : reg ≠ 10#5 := by bv_omega
    have h11 : reg ≠ 11#5 := by bv_omega
    have h31 : reg ≠ 31#5 := by bv_omega
    cases path <;>
      simp [finished, FinishPath.ops, block, Op.effect, put, next,
        state_simp_rules, h2, h9, h10, h11, h31]
  · intro reg low high
    cases path <;>
      simp [finished, FinishPath.ops, block, Op.effect, put, next, state_simp_rules]

theorem finish_frame (path : FinishPath) (s : ArmState) (base : BitVec 64)
    (space : FinishSpace s) : MemoryFrame (finishWrites path s) s (finished path base s) := by
  obtain ⟨stack, output, separate⟩ := space
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat, path.bytes) (by simp [finishWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [finishWrites])
  cases path <;> simp only [FinishPath.bytes] at out <;>
    u128_finish_expand <;> (try u128_finish_reads) <;>
    simp (disch := u128_finish_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem append_toNat (hi lo : BitVec 64) :
    (hi ++ lo).toNat = 2^64 * hi.toNat + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt hi.toNat,
    Nat.shiftLeft_eq, Nat.mul_comm]

theorem append_low (hi lo : BitVec 64) : ((hi ++ lo).setWidth 64).toNat = lo.toNat := by
  rw [BitVec.toNat_setWidth, append_toNat]
  have bound := lo.isLt
  omega

theorem append_high (hi lo : BitVec 64) :
    (((hi ++ lo) >>> (64 : Nat)).setWidth 64).toNat = hi.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, append_toNat, Nat.shiftRight_eq_div_pow]
  have hb := hi.isLt
  have lb := lo.isLt
  omega

theorem widened_low (lo : BitVec 64) : ((lo.setWidth 128).setWidth 64).toNat = lo.toNat := by
  simp only [BitVec.toNat_setWidth]
  have bound := lo.isLt
  omega

theorem widened_high (lo : BitVec 64) :
    (((lo.setWidth 128) >>> (64 : Nat)).setWidth 64).toNat = 0 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have bound := lo.isLt
  omega

/-- The None continuation defines only its sixteen-byte discriminant. -/
theorem finish_result (path : FinishPath) (s : ArmState) (base : BitVec 64)
    (space : FinishSpace s) :
    SszNative.NatNarrow.U128ResultAt (widthLoad (finished path base s))
      (r (.GPR 0#5) s).toNat (path.value s) := by
  obtain ⟨stack, output, separate⟩ := space
  cases path <;>
    simp only [FinishPath.value, SszNative.NatNarrow.U128ResultAt,
      widened_low, widened_high]
  all_goals
    repeat' constructor
    all_goals
      simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
      u128_finish_expand
      u128_finish_reads
      all_goals first
      | rfl
      | exact congrArg some (SszArm.NatToU128.append_low
          (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) (r (.GPR 8#5) s)).symm
      | exact congrArg some (SszArm.NatToU128.append_high
          (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) (r (.GPR 8#5) s)).symm

end SszArm.NatToU128
