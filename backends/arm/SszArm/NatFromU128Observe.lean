import SszArm.NatFromU128Bodies
import SszArm.NatDivisionMemory

namespace SszArm.NatFromU128

open UintCodec (widthLoad)
open Delimited (Span MemoryFrame Returned)

def pointer (s : ArmState) : BitVec 64 := r (.GPR 9#5) s + r (.GPR 10#5) s

def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 16, 16)]

def successWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 16), ((r (.GPR 0#5) s).toNat + 64, 4),
   ((r (.GPR 31#5) s).toNat - 16, 16)]

structure WideSpace (s : ArmState) extends Space s where
  header : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  positive : 0 < (pointer s).toNat
  aligned : (pointer s).toNat % 8 = 0
  payload : (pointer s).toNat + 16 ≤ 2^64
  payloadOutput : (pointer s).toNat + 16 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 68 ≤ (pointer s).toNat
  payloadStack : (pointer s).toNat + 16 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (pointer s).toNat
  payloadHeader : (pointer s).toNat + 16 ≤ (r (.GPR 4#5) s).toNat ∨
    (r (.GPR 4#5) s).toNat + 24 ≤ (pointer s).toNat
  headerOutput : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 4#5) s).toNat
  headerStack : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 4#5) s).toNat

macro "from128_memory" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := first | decide | from128_side)
    [Body.final, Body.memory, smallMemory, failureMemory, wideMemory, commitMemory,
     lowerMemory, lowerSaved, LowerKind.offset, state_simp_rules,
     ArmState.mem_w_eq_mem, BitVec.add_assoc, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.setWidth_ofNat_of_le, UintCodec.Tail.write_pair_words,
     BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint])

theorem body_returned (body : Body) (s : ArmState) (he : read_err s = .None) :
    Returned s (body.final s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Body.final, state_simp_rules]
  · cases body <;> simpa [Body.final, Body.memory, smallMemory, failureMemory,
      wideMemory, commitMemory, lowerMemory, lowerSaved, state_simp_rules] using he
  · cases body <;> simp [Body.final, Body.memory, smallMemory, failureMemory,
      wideMemory, commitMemory, lowerMemory, lowerSaved, state_simp_rules]
  · intro reg low high
    have h2 : reg ≠ 2#5 := by bv_omega
    have h8 : reg ≠ 8#5 := by bv_omega
    have h9 : reg ≠ 9#5 := by bv_omega
    cases body <;> simp [Body.final, Body.memory, smallMemory, failureMemory,
      wideMemory, commitMemory, lowerMemory, lowerSaved, state_simp_rules, h2, h8, h9]
  · intro reg low high
    cases body <;> simp [Body.final, Body.memory, smallMemory, failureMemory,
      wideMemory, commitMemory, lowerMemory, lowerSaved, state_simp_rules]

theorem body_program (body : Body) (s : ArmState) : (body.final s).program = s.program := by
  cases body <;> simp [Body.final, Body.memory, smallMemory, failureMemory,
    wideMemory, commitMemory, lowerMemory, lowerSaved, state_simp_rules]

theorem body_registers (body : Body) (s : ArmState) (reg : BitVec 5)
    (keep : reg ∉ [2#5, 8#5, 9#5]) : r (.GPR reg) (body.final s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at keep
  cases body <;> simp (disch := simp_all) [Body.final, Body.memory, smallMemory,
    failureMemory, wideMemory, commitMemory, lowerMemory, lowerSaved, state_simp_rules]

theorem small_result (s : ArmState) (space : Space s) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (Body.small.final s))
      (r (.GPR 0#5) s).toNat (.ok (.small (r (.GPR 2#5) s))) := by
  obtain ⟨stack, output, separate⟩ := space
  simp only [SszNative.NatArithmetic.AddResultAt, SszNative.NatArithmetic.operandAt,
    SszNative.NatOperand.pointer, SszNative.NatOperand.payload, SszNative.NatOperand.At]
  repeat' constructor
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    from128_memory

theorem failure_result (s : ArmState) (space : Space s) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (Body.failure.final s))
      (r (.GPR 0#5) s).toNat (.error .scratchExhausted) := by
  obtain ⟨stack, output, separate⟩ := space
  simp only [SszNative.NatArithmetic.AddResultAt, SszNative.NatArithmetic.errorAt]
  repeat' constructor
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    from128_memory

theorem small_frame (s : ArmState) (space : Space s) :
    MemoryFrame (successWrites s) s (Body.small.final s) := by
  obtain ⟨stack, output, separate⟩ := space
  intro a outside
  have pair := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [successWrites])
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [successWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [successWrites])
  from128_memory
  all_goals simp (disch := first | decide | from128_side)
    [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem, state_simp_rules]

theorem failure_frame (s : ArmState) (space : Space s) :
    MemoryFrame (localWrites s) s (Body.failure.final s) := by
  obtain ⟨stack, output, separate⟩ := space
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  from128_memory
  all_goals simp (disch := first | decide | from128_side)
    [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem, state_simp_rules]

def wideWrites (s : ArmState) : List Span := successWrites s ++
  [((r (.GPR 4#5) s).toNat + 16, 8), ((pointer s).toNat, 16)]

theorem wide_frame (s : ArmState) (space : WideSpace s) :
    MemoryFrame (wideWrites s) s (Body.wide.final s) := by
  rcases space with ⟨⟨stack, output, separate⟩, header, positive, aligned,
    payload, payloadOutput, payloadStack, payloadHeader, headerOutput, headerStack⟩
  intro a outside
  have pair := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [wideWrites, successWrites])
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [wideWrites, successWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [wideWrites, successWrites])
  have cursor := outside ((r (.GPR 4#5) s).toNat + 16, 8) (by simp [wideWrites])
  have words := outside ((pointer s).toNat, 16) (by simp [wideWrites])
  unfold pointer at *
  from128_memory
  all_goals simp (disch := first | decide | from128_side)
    [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem, state_simp_rules]

theorem wide_cursor (s : ArmState) (space : WideSpace s) :
    read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (Body.wide.final s) = r (.GPR 11#5) s := by
  rcases space with ⟨⟨stack, output, separate⟩, header, positive, aligned,
    payload, payloadOutput, payloadStack, payloadHeader, headerOutput, headerStack⟩
  unfold pointer at *
  from128_memory

theorem wide_result (s : ArmState) (space : WideSpace s) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (Body.wide.final s))
      (r (.GPR 0#5) s).toNat
      (.ok (.large (pointer s) [r (.GPR 2#5) s, r (.GPR 3#5) s])) := by
  rcases space with ⟨⟨stack, output, separate⟩, header, positive, aligned,
    payload, payloadOutput, payloadStack, payloadHeader, headerOutput, headerStack⟩
  refine ⟨⟨?_, ?_, positive, aligned, ?_, ?_⟩, ?_⟩
  · simp only [widthLoad, SszNative.NatOperand.pointer, BitVec.ofNat_toNat]
    unfold pointer at *
    from128_memory
  · simp only [widthLoad, SszNative.NatOperand.payload, BitVec.ofNat_add,
      BitVec.ofNat_toNat, List.length_cons, List.length_nil]
    unfold pointer at *
    from128_memory
  · simpa using payload
  · intro i
    have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; simp only [List.length_cons, List.length_nil] at this; omega
    rcases hi with hi | hi
    all_goals
      simp only [widthLoad, hi, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
        BitVec.ofNat_add, BitVec.ofNat_toNat]
      unfold pointer at *
      from128_memory
      all_goals simp [hi]
  · simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    unfold pointer at *
    from128_memory

end SszArm.NatFromU128
