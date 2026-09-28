import SszArm.SerializeFinishCapacity
import SszArm.EmitMemory

namespace SszArm.Serialize.Finish

open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

/-- Result is disjoint from the live staging, Plan, and saved activation intervals. -/
structure MeasureSpace (s : ArmState) : Prop where
  stackHigh : (sp s).toNat + 144 ≤ 2^64
  resultHigh : (result s).toNat + 72 ≤ 2^64
  separate : (result s).toNat + 72 ≤ (sp s).toNat + 8 ∨
    (sp s).toNat + 144 ≤ (result s).toNat

def measureCopyOps : List Op :=
  [.p76, .p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108, .p112]

def measureCopied (base : BitVec 64) (s : ArmState) : ArmState :=
  block base measureCopyOps (branched base s)

def measureReturned (base : BitVec 64) (s : ArmState) : ArmState :=
  returned (measureCopied base s)

def measureMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (result s) (read_mem_bytes 16 (sp s + 24#64) s)
  (write_mem_bytes 8 (result s + 64#64) (read_mem_bytes 8 (sp s + 88#64) s)
  (write_mem_bytes 8 (result s + 32#64) (read_mem_bytes 8 (sp s + 56#64) s)
  (write_mem_bytes 16 (result s + 40#64) (read_mem_bytes 16 (sp s + 64#64) s)
  (write_mem_bytes 8 (result s + 56#64) (read_mem_bytes 8 (sp s + 80#64) s)
  (write_mem_bytes 16 (result s + 16#64) (read_mem_bytes 16 (sp s + 40#64) s)
  (stageMemory s))))))

theorem measure_copy_run (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 52#64)
    (status : read_mem_bytes 4 (sp s + 88#64) s ≠ 0#32) :
    run 16 s = measureCopied base s := by
  rw [show 16 = 6 + 10 by decide, run_plus, branch_run base s code error aligned pc]
  apply block_run base measureCopyOps (branched base s)
  · exact code.congr (by simp [branched, staged, state_simp_rules])
  · exact (branched_error base s).trans error
  · simpa [branched, staged, stageOps, block, Op.effect, next, put,
      CheckSPAlignment, read_gpr, state_simp_rules] using aligned
  · simp [Follows, measureCopyOps, branched, Op.row, Op.effect, next, put,
      state_simp_rules, status, BitVec.add_assoc]

@[simp] theorem measure_copied_pc (base : BitVec 64) (s : ArmState)
    (status : read_mem_bytes 4 (sp s + 88#64) s ≠ 0#32) :
    read_pc (measureCopied base s) = base + 116#64 := by
  simp [measureCopied, measureCopyOps, branched, block, Op.effect, next, put,
    state_simp_rules, status, BitVec.add_assoc]

@[simp] theorem measure_copied_program (base : BitVec 64) (s : ArmState) :
    (measureCopied base s).program = s.program := by
  simp [measureCopied, branched, staged, state_simp_rules]

@[simp] theorem measure_copied_error (base : BitVec 64) (s : ArmState) :
    read_err (measureCopied base s) = read_err s := by
  rw [measureCopied, block_error, branched_error]

@[simp] theorem measure_copied_vector (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (measureCopied base s) = r (.SFP reg) s := by
  simp [measureCopied, branched, staged, state_simp_rules]

theorem measure_copied_register (base : BitVec 64) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [5#5, 8#5, 9#5, 10#5, 11#5, 12#5, 13#5]) :
    r (.GPR reg) (measureCopied base s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  simp_all [measureCopied, measureCopyOps, branched, staged, stageOps, block,
    Op.effect, next, put, state_simp_rules]

@[simp] theorem measure_copied_sp (base : BitVec 64) (s : ArmState) :
    sp (measureCopied base s) = sp s := measure_copied_register base s _ (by decide)

/-- Original PC52 through the original measurement-error RET at132. -/
theorem measure_return_run (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 52#64)
    (status : read_mem_bytes 4 (sp s + 88#64) s ≠ 0#32) :
    run 21 s = measureReturned base s := by
  rw [show 21 = 16 + 5 by decide, run_plus,
    measure_copy_run base s code error aligned pc status]
  apply return_run .measurement
  · exact code.congr (measure_copied_program base s)
  · exact (measure_copied_error base s).trans error
  · simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, measure_copied_sp] using aligned
  · exact measure_copied_pc base s status

private def copyFirst (s : ArmState) : ArmState :=
  write_mem_bytes 16 (result s + 16#64) (r (.GPR 5#5) s ++ r (.GPR 8#5) s) s

private def copyMiddle (s : ArmState) : ArmState :=
  write_mem_bytes 16 (result s + 40#64)
    (read_mem_bytes 8 (sp s + 72#64) s ++ read_mem_bytes 8 (sp s + 64#64) s)
    (write_mem_bytes 8 (result s + 56#64) (read_mem_bytes 8 (sp s + 80#64) s)
      (copyFirst s))

private def copyTail (s : ArmState) : ArmState :=
  write_mem_bytes 16 (result s)
    (read_mem_bytes 8 (sp s + 16#64) (copyMiddle s) ++
      read_mem_bytes 8 (sp s + 8#64) (copyMiddle s))
    (write_mem_bytes 8 (result s + 64#64)
      (read_mem_bytes 4 (sp s + 92#64) (copyFirst s) ++ (r (.GPR 9#5) s).setWidth 32)
      (write_mem_bytes 8 (result s + 32#64) (r (.GPR 10#5) s) (copyMiddle s)))

private theorem copy_block_memory (base : BitVec 64) (s : ArmState) :
    (block base measureCopyOps s).mem = (copyTail s).mem := by
  simp only [measureCopyOps, block, List.foldl_cons, List.foldl_nil]
  simp [Op.effect, next, put, copyTail, copyMiddle, copyFirst, sp, result,
    state_simp_rules, BitVec.setWidth_setWidth_of_le]
  simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

private theorem stack_read_result_store (s t : ArmState) (space : MeasureSpace s)
    (bytes offset storeBytes storeOffset : Nat) (value : BitVec (storeBytes * 8))
    (low : 8 ≤ offset) (high : offset + bytes ≤ 144)
    (storeHigh : storeOffset + storeBytes ≤ 72) :
    read_mem_bytes bytes (sp s + BitVec.ofNat 64 offset)
      (write_mem_bytes storeBytes (result s + BitVec.ofNat 64 storeOffset) value t) =
        read_mem_bytes bytes (sp s + BitVec.ofNat 64 offset) t := by
  rcases space with ⟨stackHigh, resultHigh, separate⟩
  exact BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ _ _ _ _ _
    (by bv_omega) (by bv_omega) (by rcases separate with h | h <;> bv_omega)

private theorem branched_original_read (base : BitVec 64) (s : ArmState)
    (space : MeasureSpace s) (bytes offset : Nat)
    (low : 24 ≤ offset) (high : offset + bytes ≤ 144) :
    read_mem_bytes bytes (sp s + BitVec.ofNat 64 offset) (branched base s) =
      read_mem_bytes bytes (sp s + BitVec.ofNat 64 offset) s := by
  by_cases empty : bytes = 0
  · subst bytes
    simp [read_mem_bytes]
  have bound := space.stackHigh
  have offsetBound : offset < 2^64 := by omega
  have sumBound : (sp s).toNat + offset < 2^64 := by omega
  have frame := stage_frame base s (by omega)
  simp only [branched, state_simp_rules]
  apply frame.read _ bytes (by bv_omega)
  right
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  right
  dsimp
  bv_omega

private theorem branched_leading (base : BitVec 64) (s : ArmState)
    (space : MeasureSpace s) :
    read_mem_bytes 8 (sp s + 8#64) (branched base s) = read_mem_bytes 8 (sp s + 24#64) s ∧
    read_mem_bytes 8 (sp s + 16#64) (branched base s) = read_mem_bytes 8 (sp s + 32#64) s := by
  have bound := space.stackHigh
  have pair : stageMemory s =
      write_mem_bytes 8 (sp s + 16#64) (read_mem_bytes 8 (sp s + 32#64) s)
        (write_mem_bytes 8 (sp s + 8#64) (read_mem_bytes 8 (sp s + 24#64) s) s) := by
    unfold stageMemory
    rw [UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega)]
    simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp only [branched, state_simp_rules]
  simp only [Memory.mem_eq_iff_read_mem_bytes_eq.mp (staged_memory base s), pair]
  constructor
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (sp s + 8#64) (sp s + 16#64) _ (by bv_omega) (by bv_omega) (by left; bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  · exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

/-- PC100 reloads after three result stores. Separation proves, rather than assumes,
that it recovers the staged leading words; PC88 still reads arbitrary Plan tail bytes. -/
theorem measure_copied_memory (base : BitVec 64) (s : ArmState) (space : MeasureSpace s) :
    (measureCopied base s).mem = (measureMemory s).mem := by
  have stack : sp (branched base s) = sp s := by
    simp [sp, branched, state_simp_rules]
  have output : result (branched base s) = result s := by
    simp [result, branched, state_simp_rules]
  have fields :
      r (.GPR 8#5) (branched base s) = read_mem_bytes 8 (sp s + 40#64) s ∧
      r (.GPR 5#5) (branched base s) = read_mem_bytes 8 (sp s + 48#64) s ∧
      r (.GPR 10#5) (branched base s) = read_mem_bytes 8 (sp s + 56#64) s ∧
      (r (.GPR 9#5) (branched base s)).setWidth 32 = read_mem_bytes 4 (sp s + 88#64) s := by
    simpa [branched, state_simp_rules] using staged_fields base s
  have branchMemory : (branched base s).mem = (stageMemory s).mem := by
    simp [branched, state_simp_rules]
  have leading := branched_leading base s space
  have firstRead : read_mem_bytes 4 (sp s + 92#64) (copyFirst (branched base s)) =
      read_mem_bytes 4 (sp s + 92#64) s := by
    unfold copyFirst
    rw [output, stack_read_result_store s _ space 4 92 16 16 _ (by decide) (by decide) (by decide)]
    exact branched_original_read base s space 4 92 (by decide) (by decide)
  have middleRead (offset : Nat) (low : 8 ≤ offset) (high : offset + 8 ≤ 144) :
      read_mem_bytes 8 (sp s + BitVec.ofNat 64 offset) (copyMiddle (branched base s)) =
        read_mem_bytes 8 (sp s + BitVec.ofNat 64 offset) (branched base s) := by
    unfold copyMiddle copyFirst
    simp only [output]
    rw [stack_read_result_store s _ space 8 offset 16 40 _ low high (by decide)]
    rw [stack_read_result_store s _ space 8 offset 8 56 _ low high (by decide)]
    rw [stack_read_result_store s _ space 8 offset 16 16 _ low high (by decide)]
  have lowRead := (middleRead 8 (by decide) (by decide)).trans leading.1
  have highRead := (middleRead 16 (by decide) (by decide)).trans leading.2
  have read64 := branched_original_read base s space 8 64 (by decide) (by decide)
  have read72 := branched_original_read base s space 8 72 (by decide) (by decide)
  have read80 := branched_original_read base s space 8 80 (by decide) (by decide)
  rw [measureCopied, copy_block_memory]
  simp only [copyTail, stack, output, firstRead, lowRead, highRead]
  simp [copyMiddle, copyFirst, stack, output, read64, read72, read80,
    fields.1, fields.2.1, fields.2.2.1, fields.2.2.2,
    measureMemory, BoolCodec.pair_read, pair_read_dwords,
    BitVec.add_assoc, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem,
    branchMemory]

def measureWrites (s : ArmState) : List (Nat × Nat) :=
  [((sp s).toNat + 8, 16), ((result s).toNat, 72)]

theorem measure_copy_frame (base : BitVec 64) (s : ArmState) (space : MeasureSpace s) :
    MemoryFrame (measureWrites s) s (measureCopied base s) := by
  rcases space with ⟨stackHigh, resultHigh, separate⟩
  intro address outside
  have stackOutside := outside ((sp s).toNat + 8, 16) (by simp [measureWrites])
  have resultOutside := outside ((result s).toNat, 72) (by simp [measureWrites])
  rw [measure_copied_memory base s ⟨stackHigh, resultHigh, separate⟩]
  simp (disch := serialize_finish_side)
    [measureMemory, stageMemory, BoolCodec.write_mem_bytes_frame]

theorem measure_return_frame (base : BitVec 64) (s : ArmState) (space : MeasureSpace s) :
    MemoryFrame (measureWrites s) s (measureReturned base s) := by
  intro address outside
  simp only [measureReturned, returned_memory]
  exact measure_copy_frame base s space address outside

/-- All nine words are copied, including the unconstrained final four padding bytes. -/
theorem measure_return_word (base : BitVec 64) (s : ArmState) (space : MeasureSpace s)
    (index : Fin 9) :
    read_mem_bytes 8 (result s + BitVec.ofNat 64 (8 * index.val)) (measureReturned base s) =
      read_mem_bytes 8 (sp s + BitVec.ofNat 64 (24 + 8 * index.val)) s := by
  have memory : (measureReturned base s).mem = (measureMemory s).mem := by
    simpa only [measureReturned, returned_memory] using measure_copied_memory base s space
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp memory]
  rcases space with ⟨stackHigh, resultHigh, separate⟩
  rcases index with ⟨index, bound⟩
  have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
  rcases indices with h | h | h | h | h | h | h | h | h <;> subst index <;>
    simp (disch := serialize_finish_side)
      [measureMemory, stageMemory, BoolCodec.pair_read, UintCodec.Tail.write_pair_words,
        BitVec.add_assoc, BoolCodec.read_mem_bytes_write_mem_bytes_same,
        BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem measure_return_byte (base : BitVec 64) (s : ArmState) (space : MeasureSpace s)
    (index : Nat) (within : index < 72) :
    (measureReturned base s).mem (result s + BitVec.ofNat 64 index) =
      s.mem (sp s + BitVec.ofNat 64 (24 + index)) := by
  have selected : index / 8 < 9 := by omega
  have copied := measure_return_word base s space ⟨index / 8, selected⟩
  have byte := copied_word_byte s (measureReturned base s)
    (sp s + BitVec.ofNat 64 (24 + 8 * (index / 8)))
    (result s + BitVec.ofNat 64 (8 * (index / 8))) 8 (index % 8)
    (by have := space.stackHigh; bv_omega)
    (by have := space.resultHigh; bv_omega) (Nat.mod_lt _ (by decide)) copied
  have splitIndex : 8 * (index / 8) + index % 8 = index := by omega
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc, splitIndex] using byte

theorem measure_return_read (base : BitVec 64) (s : ArmState) (space : MeasureSpace s)
    (displacement bytes : Nat) (within : displacement + bytes ≤ 72) :
    read_mem_bytes bytes (result s + BitVec.ofNat 64 displacement) (measureReturned base s) =
      read_mem_bytes bytes (sp s + BitVec.ofNat 64 (24 + displacement)) s := by
  apply BitVec.eq_of_extractLsByte_eq
  intro index
  by_cases small : index < bytes
  · have sourceBound : (sp s + BitVec.ofNat 64 (24 + displacement)).toNat + bytes ≤ 2^64 := by
      have := space.stackHigh; bv_omega
    have targetBound : (result s + BitVec.ofNat 64 displacement).toNat + bytes ≤ 2^64 := by
      have := space.resultHigh; bv_omega
    simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
      Memory.extractLsByte_read_bytes targetBound,
      Memory.extractLsByte_read_bytes sourceBound, if_pos small]
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc, Memory.read, read_store] using
      measure_return_byte base s space (displacement + index) (by omega)
  · rw [BitVec.extractLsByte_ge (by omega), BitVec.extractLsByte_ge (by omega)]

/-- The copy transports the entire error image. Borrowed limbs are protected by
original local geometry, not by a hypothesis about any later helper execution. -/
theorem measure_error_at (base : BitVec 64) (s : ArmState) (space : MeasureSpace s)
    (reason : SszNative.Serialize.Error)
    (input : Measure.ErrorAt (widthLoad s) ((sp s).toNat + 24) reason)
    (leftOwned : NatDivision.OperandOwned (measureWrites s) (Measure.errorOperands reason).1)
    (rightOwned : NatDivision.OperandOwned (measureWrites s) (Measure.errorOperands reason).2) :
    Measure.ErrorAt (widthLoad (measureReturned base s)) (result s).toNat reason := by
  have fields (displacement bytes : Nat) (within : displacement + bytes ≤ 72) :
      widthLoad (measureReturned base s) ((result s).toNat + displacement) bytes =
        widthLoad s ((sp s).toNat + 24 + displacement) bytes := by
    unfold widthLoad
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]
    simp only [BitVec.setWidth_eq]
    have sourceAddress : BitVec.ofNat 64 ((sp s).toNat + 24 + displacement) =
        sp s + BitVec.ofNat 64 (24 + displacement) := by
      simp [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_assoc]
    rw [sourceAddress, measure_return_read base s space displacement bytes within]
  obtain ⟨tag, length, left, right, zero48, zero56, status⟩ := input
  have frame := measure_return_frame base s space
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using (fields 0 8 (by decide)).trans tag
  · exact (fields 8 8 (by decide)).trans length
  · exact (fields 16 8 (by decide)).trans left.1
  · simpa only [Nat.add_assoc] using
      (fields 24 8 (by decide)).trans (by simpa only [Nat.add_assoc] using left.2.1)
  · exact NatDivision.operand_at_preserved frame _ left.2.2 leftOwned
  · exact (fields 32 8 (by decide)).trans right.1
  · simpa only [Nat.add_assoc] using
      (fields 40 8 (by decide)).trans (by simpa only [Nat.add_assoc] using right.2.1)
  · exact NatDivision.operand_at_preserved frame _ right.2.2 rightOwned
  · exact (fields 48 8 (by decide)).trans zero48
  · exact (fields 56 8 (by decide)).trans zero56
  · exact (fields 64 4 (by decide)).trans status

end SszArm.Serialize.Finish
