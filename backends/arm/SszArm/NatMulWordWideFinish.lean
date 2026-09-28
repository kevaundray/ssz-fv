import SszArm.NatMulWordSmallMemory

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected Returned)
open SszNative.NatArithmetic

 theorem wide_commit_abi (s : ArmState) (base : BitVec 64) :
    SmallABI s (block base Reserve.wideCommitOps s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg keep
    apply Reserve.wide_commit_registers
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  · intro reg
    exact Reserve.block_preserves (r (.SFP reg)) base Reserve.wideCommitOps
      (fun op _ t => op.sfp base t reg) s

/-- Finish the actual cursor/pair stores and original wide RET. All stored bytes
are derived from PC1204/1208; no initialized-scratch premise is used. -/
 theorem wide_success_finish (s u : ArmState) (base factor low high : BitVec 64)
    (operand : SszNative.NatOperand) (reservation : SszNative.Arena.Reservation)
    (owned : Owned s operand factor) (priorFrame : SmallFrame s u)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc u = base + 1200#64) (space : Reserve.WideSpace u)
    (lowReg : r (.GPR 8#5) u = low) (highReg : r (.GPR 9#5) u = high)
    (nonzero : high ≠ 0#64) (pointer : (Reserve.widePointer u).toNat = reservation.pointer)
    (finish : (r (.GPR 12#5) u).toNat = reservation.used)
    (model : outcome s operand factor = committed reservation [low, high]) :
    ∃ t, run 16 u = t ∧ Post s t operand factor := by
  let v := block base Reserve.wideCommitOps u
  have vabi : SmallABI s v := priorFrame.toSmallABI.trans (wide_commit_abi u base)
  have vr := Reserve.wide_commit_run u base (priorFrame.code code) (priorFrame.error.trans error)
    (priorFrame.aligned aligned) pc
  have ve := Reserve.wide_commit_effect u base pc
  have vm := Reserve.wide_commit_memory u base space pc
  have pointerEq : BitVec.ofNat 64 reservation.pointer = Reserve.widePointer u := by
    rw [← pointer, BitVec.ofNat_toNat]
  have resultEq : (outcome s operand factor).result =
      .ok (.large (Reserve.widePointer u) [low, high]) := by
    simp [model, committed, pointerEq, SszNative.NatOperand.fromWords,
      SszNative.Limbs.trim, nonzero]
  have fresh := owned.fresh reservation (by simp [model, committed])
  have payloadLocal : Protected (localWrites s (outcome s operand factor)) reservation.pointer 16 := by
    rcases fresh with empty | apart
    · simp [model, committed] at empty
    · right
      intro span member
      simpa [model, committed] using apart span (List.mem_append_left _ member)
  have payloadReturn : Protected (valueWrites v) (Reserve.widePointer u).toNat 16 := by
    rw [pointer]
    exact small_value_protected vabi owned.stackBound _ _ resultEq _ _ payloadLocal
  have payloadAt : (SszNative.NatOperand.large (Reserve.widePointer u) [low, high]).At (widthLoad v) := by
    simpa only [lowReg, highReg] using vm.2.2.2.2
  have returned := value_run_contract .wide v base (vabi.code code) (vabi.error.trans error)
    (vabi.aligned aligned) ve.1 (vabi.return_owned owned.return_owned)
    (.large (Reserve.widePointer u) [low, high]) ve.2.1 ve.2.2.1 payloadAt
    (by simpa only [NatAdd.OperandOwned, List.length_cons, List.length_nil] using payloadReturn)
  let t := valueResult .wide base v
  have currentHeader : Protected (valueWrites v) (r (.GPR 4#5) s).toNat 24 :=
    small_value_protected vabi owned.stackBound _ _ resultEq _ _ owned.arenaLocal
  have physical := owned.arenaBound
  have header16 : (r (.GPR 4#5) s + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by bv_omega
  have header8 : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by bv_omega
  have cursorReturn := returned.2.2.2.read (r (.GPR 4#5) s + 16#64) 8
    (by rw [header16]; omega) (by rw [header16]; exact currentHeader.subspan 16 8 (by decide))
  have baseReturn := returned.2.2.2.read (r (.GPR 4#5) s) 8
    (by omega) (by simpa using currentHeader.subspan 0 8 (by decide))
  have capReturn := returned.2.2.2.read (r (.GPR 4#5) s + 8#64) 8
    (by rw [header8]; omega) (by rw [header8]; exact currentHeader.subspan 8 8 (by decide))
  have commitFrame : MemoryFrame (writesFor s (outcome s operand factor)) u v := by
    apply vm.1.weaken
    intro span member
    simp only [Reserve.wideCommitWrites, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · simp [writesFor, model, committed, priorFrame.arena, header16]
    · simp [writesFor, model, committed, pointer]
  have frame : MemoryFrame (writesFor s (outcome s operand factor)) s t :=
    ((priorFrame.full _).trans commitFrame).trans
      (small_value_frame vabi owned.stackBound _ _ resultEq returned.2.2.2)
  refine ⟨t, ?_, ?_⟩
  · change run (4 + 12) u = t
    rw [run_plus, vr]
    exact returned.1
  · refine ⟨vabi.returned returned.2.1, ?_, ?_, ?_, frame,
      NatAdd.operand_preserved frame operand owned.operandAt owned.inputOwned, ?_, ?_⟩
    · simpa only [resultEq, vabi.out] using returned.2.2.1
    · intro allocation allocated
      have same : allocation = reservation := by
        simpa only [model, committed, Option.some.injEq] using allocated.symm
      subst allocation
      have stored := returned.2.2.1.1.2.2.2.2.2
      simpa only [model, committed, pointer] using stored
    · rw [cursorReturn, ← priorFrame.arena, vm.2.1, model]
      exact finish
    · rw [baseReturn, ← priorFrame.arena, vm.2.2.1]
      simpa using priorFrame.header owned 0 (by decide)
    · rw [capReturn, ← priorFrame.arena, vm.2.2.2.1]
      exact priorFrame.header owned 8 (by decide)

end SszArm.NatMulWord
