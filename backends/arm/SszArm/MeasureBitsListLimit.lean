import SszArm.MeasureBitsListPrefix
import SszArm.MeasureBitsLimitFields
import SszArm.MeasureHelpersResultSpace

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (Span Protected MemoryFrame)

theorem limit_executes (schema : Schema) (s u : ArmState) (args : Args) (bits : Packed)
    (actual cap : NatOperand) (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual) (present : schema.cap = some cap)
    (over : ¬ actual.value ≤ cap.value) (code : CodeAt u base) (error : read_err u = .None)
    (aligned : CheckSPAlignment u) (pc : read_pc u = base + 1744#64) :
    ∃ t, run 29 u = t ∧ Produced s t args schema.descriptor (.bits bits) base := by
  have counted : (SszNative.Serialize.fromWide (arenaOf s args) bits.count).result = .ok actual := by
    change (countCall s args bits).result.mapError _ = _
    simp only [pre.counted, Except.mapError]
  have measured : outcome s args schema.descriptor (.bits bits) =
      ⟨.error (.limit cap actual), (countCall s args bits).used, [countCall s args bits]⟩ := by
    rw [list_outcome, present]
    simpa only [SszNative.Serialize.fromWide, countCall] using
      SszNative.Serialize.measureList_limit_no_rollback cap actual bits (arenaOf s args) counted over
  have space := Helpers.original_error_space owned u pre.core.result pre.core.stack (.limit cap actual)
    (by simp only [measured])
  have position : (r (.GPR 31#5) u).toNat - 16 = args.stack.toNat - 288 := by
    have low := owned.stackLow
    rw [pre.core.stack, Args.bodySP]
    bv_omega
  have writerLocal : ∀ span ∈ Result.errorWrites u,
      span ∈ localWrites args (outcome s args schema.descriptor (.bits bits)) := by
    intro span member
    simp only [Result.errorWrites, position, pre.core.result, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp [localWrites, stackWrites, bodyStackWrites]
    · simp [localWrites, resultWrites, measured, resultExtent, propagated]
  have writerBody : ∀ span ∈ Result.errorWrites u,
      span ∈ bodyWrites args (outcome s args schema.descriptor (.bits bits)) := by
    intro span member
    simp only [Result.errorWrites, position, pre.core.result, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp [bodyWrites, bodyStackWrites]
    · simp [bodyWrites, resultWrites, measured, resultExtent, propagated]
  have free : Protected (Result.errorWrites u)
      ((arenaOf s args).base + (arenaOf s args).used)
      ((arenaOf s args).capacity - (arenaOf s args).used) := by
    rcases owned.freeLocal with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (List.mem_append.mpr (Or.inl (writerLocal span member))))
  have headerOwned : Protected (Result.errorWrites u) args.arena.toNat 24 := by
    rcases owned.headerLocal with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (writerLocal span member))
  have capRegisters : r (.GPR 22#5) u = cap.pointer ∧ r (.GPR 23#5) u = cap.payload := by
    simpa only [present] using pre.core.cap
  have capOwned : NatDivision.OperandOwned (Result.errorWrites u) cap := by
    apply operand_owned_restrict cap (owned.operandOwned cap
      (List.mem_append.mpr (Or.inl (cap_member schema cap present))))
    intro span member
    exact List.mem_append.mpr (Or.inl (writerLocal span member))
  have actualOwned := Helpers.fromWide_result_owned (Result.errorWrites u) (arenaOf s args) bits.count
    owned.storageBound free actual pre.counted
  let t := Limit.result u base
  have writerFrame := Limit.result_frame u base space
  have stored := Limit.result_at u base space cap actual capRegisters.1 capRegisters.2
    pre.core.pointer pre.core.payload (Prefix.cap_at owned pre cap present) pre.actualAt capOwned actualOwned
  have r0 := Emit.frame_read_offset writerFrame args.arena 24 0 8 owned.arenaBound headerOwned (by decide)
  have r8 := Emit.frame_read_offset writerFrame args.arena 24 8 8 owned.arenaBound headerOwned (by decide)
  have r16 := Emit.frame_read_offset writerFrame args.arena 24 16 8 owned.arenaBound headerOwned (by decide)
  simp only [BitVec.add_zero] at r0
  have written := Helpers.fromWide_written_preserved (arenaOf s args) bits.count owned.storageBound
    free writerFrame pre.written
  refine ⟨t, Limit.executes u base code error aligned pc,
    Limit.result_pc u base, (Limit.result_program u base).trans pre.program,
    (Limit.result_error u base).trans error, (Limit.result_sp u base).trans pre.core.stack,
    ?_, ?_, ⟨r0.trans pre.header.1, r8.trans pre.header.2⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [measured, pre.core.result] using stored
  · rw [r16, measured]
    exact pre.cursor
  · intro call member
    simp only [measured, List.mem_singleton] at member
    subst call
    exact written
  · have first : MemoryFrame (bodyWrites args (outcome s args schema.descriptor (.bits bits))) s u := by
      apply pre.frame.weaken
      intro span member
      simp only [prefixWrites, List.mem_append, List.mem_singleton] at member
      rcases member with rfl | allocated
      · simp [bodyWrites, bodyStackWrites]
      · exact List.mem_append.mpr (Or.inr (count_writes_subset schema s args bits span allocated))
    exact first.trans (writerFrame.weaken writerBody)
  · intro reg member
    have kept : reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 10#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (Limit.result_register u base reg kept.1 kept.2.1 kept.2.2).trans (pre.registers reg member)
  · intro reg low high
    exact congrArg (fun word : BitVec 128 => word.setWidth 64)
      ((Limit.result_vector u base reg).trans (pre.vectors reg))

end SszArm.Measure.Bits.List
