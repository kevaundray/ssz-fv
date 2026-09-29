import SszArm.CodecEmitPartsActivation
import SszArm.CodecEmitPartsStatus
import SszArm.CodecStack
import SszCodecEmit

namespace SszArm.Codec.Emit.Parts

open SszArm.Emit.Activation (next put save)
open SszArm.Emit.Dispatch (branch)
open Delimited (Span Protected MemoryFrame)

def emptyOps : List Op := [.p28, .p32, .p36, .p40, .p516, .p736]

@[irreducible] def emptyPrepared (s : ArmState) : ArmState := block emptyOps (prologue s)

@[simp] theorem emptyPrepared_program (s : ArmState) : (emptyPrepared s).program = s.program := by
  simp [emptyPrepared]

@[simp] theorem emptyPrepared_error (s : ArmState) : read_err (emptyPrepared s) = read_err s := by
  simp [emptyPrepared]

@[simp] theorem emptyPrepared_sp (s : ArmState) : r (.GPR 31#5) (emptyPrepared s) = bodySP s := by
  simp [emptyPrepared, emptyOps, block, Op.effect, put, next, save, branch, state_simp_rules]

@[simp] theorem emptyPrepared_result (s : ArmState) :
    r (.GPR 26#5) (emptyPrepared s) = r (.GPR 0#5) s := by
  simp [emptyPrepared, emptyOps, block, Op.effect, put, next, save, branch, state_simp_rules]

@[simp] theorem emptyPrepared_zero (s : ArmState) : r (.GPR 24#5) (emptyPrepared s) = 0#64 := by
  simp [emptyPrepared, emptyOps, block, Op.effect, put, next, save, branch, state_simp_rules]

@[simp] theorem emptyPrepared_x18 (s : ArmState) :
    r (.GPR 18#5) (emptyPrepared s) = r (.GPR 18#5) s := by
  simp [emptyPrepared, emptyOps, block, Op.effect, put, next, save, branch, state_simp_rules]

@[simp] theorem emptyPrepared_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (emptyPrepared s) = r (.SFP reg) s := by simp [emptyPrepared]

@[simp] theorem emptyPrepared_memory (s : ArmState) :
    (emptyPrepared s).mem =
      (write_mem_bytes 16 (bodySP s + 40#64)
        (r (.GPR 6#5) s ++ r (.GPR 5#5) s) (prologue s)).mem := by
  simp [emptyPrepared, emptyOps, block, Op.effect, put, next, save, branch, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem emptyPrepared_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base) (empty : r (.GPR 3#5) s = 0#64)
    (unplanned : r (.GPR 4#5) s = 0#64) :
    read_pc (emptyPrepared s) = base + 740#64 := by
  have pcBody : read_pc (prologue s) = base + 28#64 := by rw [prologue_pc, pc]
  change r .PC (prologue s) = _ at pcBody
  simp [emptyPrepared, emptyOps, block, Op.effect, put, next, save, branch,
    state_simp_rules, empty, unplanned, pcBody, BitVec.add_assoc]

theorem emptyPrepared_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (emptyPrepared s) :=
  CheckSPAlignment_of_r_sp_aligned (emptyPrepared_sp s) (bodySP_aligned s aligned)

theorem emptyPrepared_run (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (empty : r (.GPR 3#5) s = 0#64) (unplanned : r (.GPR 4#5) s = 0#64) :
    run 13 s = emptyPrepared s := by
  have first := prologue_run s base code error aligned pc
  have second : run 6 (prologue s) = block emptyOps (prologue s) := by
    apply runs emptyOps (prologue s) base
      (Linked.WordsAt.preserve code (prologue_program s)) ((prologue_error s).trans error)
    have alignedBody := prologue_aligned s aligned
    have pcBody : read_pc (prologue s) = base + 28#64 := by rw [prologue_pc, pc]
    change r .PC (prologue s) = _ at pcBody
    simp (config := {decide := true}) [Follows, emptyOps, Op.row, Op.effect,
      put, next, save, branch, state_simp_rules, CheckSPAlignment, read_gpr,
      BitVec.setWidth_eq, pcBody, empty, unplanned, BitVec.add_assoc] at alignedBody ⊢
    exact alignedBody
  change run (7 + 6) s = _
  rw [run_plus, first, second]
  rw [emptyPrepared]

theorem emptyPrepared_frame (s : ArmState) (low : 240 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (Stack.envelope (r (.GPR 31#5) s).toNat 240) s (emptyPrepared s) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 240, 240) (by simp [Stack.envelope])
  simp only [Prod.fst, Prod.snd] at apart
  rw [emptyPrepared_memory,
    BoolCodec.write_mem_bytes_frame _ _ 16 _ address
      (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)]
  apply prologue_frame s (by omega) address
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  simp only [Prod.fst, Prod.snd]
  omega

theorem emptyPrepared_saved (s : ArmState) (low : 240 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (emptyPrepared s) = r (.GPR reg) s := by
  have interval : 128 ≤ offset ∧ offset ≤ 216 := by
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (emptyPrepared_memory s))]
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · exact prologue_saved s (by omega) reg offset member
  all_goals simp only [bodySP]; bv_omega

/-- The empty unplanned path neither reads Parts nor any Value/Plan object. -/
def emptyReturned (s : ArmState) : ArmState := restored (finished .sequential (emptyPrepared s))

def emptyWrites (s : ArmState) : List Span :=
  Stack.envelope (r (.GPR 31#5) s).toNat 240 ++
    [((r (.GPR 0#5) s).toNat, 8), ((r (.GPR 0#5) s).toNat + 64, 4)]

theorem empty_return_run (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (empty : r (.GPR 3#5) s = 0#64) (unplanned : r (.GPR 4#5) s = 0#64) :
    run 33 s = emptyReturned s := by
  have preparedCode := Linked.WordsAt.preserve code (emptyPrepared_program s)
  have preparedError := (emptyPrepared_error s).trans error
  have preparedAligned := emptyPrepared_aligned s aligned
  have preparedPC := emptyPrepared_pc s base pc empty unplanned
  have middle := finished_run .sequential (emptyPrepared s) base preparedCode preparedError
    preparedAligned preparedPC
  have last := restored_run (finished .sequential (emptyPrepared s)) base
    (Linked.WordsAt.preserve preparedCode (finished_program _ _))
    ((finished_error _ _).trans preparedError)
    (finished_aligned _ _ preparedAligned) (finished_pc _ _ base preparedPC)
  change run (13 + (12 + 8)) s = _
  rw [run_plus, emptyPrepared_run s base code error aligned pc empty unplanned,
    run_plus, middle, last]
  rfl

theorem empty_unplanned_correct (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (empty : r (.GPR 3#5) s = 0#64) (unplanned : r (.GPR 4#5) s = 0#64)
    (low : 240 ≤ (r (.GPR 31#5) s).toNat)
    (bound : (r (.GPR 0#5) s).toNat + 68 ≤ 2 ^ 64)
    (separate : Protected (Stack.envelope (r (.GPR 31#5) s).toNat 240)
      (r (.GPR 0#5) s).toNat 68) :
    run 33 s = emptyReturned s ∧ SszArm.Emit.Returned s (emptyReturned s) ∧
      read_mem_bytes 8 (r (.GPR 0#5) s) (emptyReturned s) = 0#64 ∧
      read_mem_bytes 4 (r (.GPR 0#5) s + 64#64) (emptyReturned s) = 0#32 ∧
      MemoryFrame (emptyWrites s) s (emptyReturned s) := by
  rcases separate with impossible | separate
  · omega
  have apart := separate ((r (.GPR 31#5) s).toNat - 240, 240) (by simp [Stack.envelope])
  simp only [Prod.fst, Prod.snd] at apart
  have preparedLow : 16 ≤ (r (.GPR 31#5) (emptyPrepared s)).toNat := by
    rw [emptyPrepared_sp]
    simp only [bodySP]
    bv_omega
  have resultRegister : r (.GPR FinishKind.sequential.result) (emptyPrepared s) = r (.GPR 0#5) s := by
    change r (.GPR 26#5) (emptyPrepared s) = r (.GPR 0#5) s
    exact emptyPrepared_result s
  have sizeRegister : r (.GPR FinishKind.sequential.size) (emptyPrepared s) = 0#64 := by
    change r (.GPR 24#5) (emptyPrepared s) = 0#64
    exact emptyPrepared_zero s
  have preparedBound : (r (.GPR FinishKind.sequential.result) (emptyPrepared s)).toNat + 68 ≤ 2 ^ 64 := by
    simpa only [resultRegister] using bound
  have finishFrame := finished_frame .sequential (emptyPrepared s) preparedLow preparedBound
  have ready : RestoreReady s (finished .sequential (emptyPrepared s)) := by
    refine ⟨by simp, ?_, by simp, ?_⟩
    · intro reg offset member
      have interval : 128 ≤ offset ∧ offset ≤ 216 := by
        simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
        rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
      rw [finishFrame.read (bodySP s + BitVec.ofNat 64 offset) 8
        (by simp only [bodySP]; bv_omega)]
      · exact emptyPrepared_saved s low reg offset member
      · right
        intro span member
        simp only [finishWrites, resultRegister, emptyPrepared_sp,
          List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd, bodySP] <;> bv_omega
    · intro reg _ _
      simp
  have returned := restored_returns s (finished .sequential (emptyPrepared s)) ready
    (by simpa using error) (by simp)
  have length := finished_length .sequential (emptyPrepared s) preparedLow preparedBound
    (by
      right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp only [resultRegister, emptyPrepared_sp, Prod.fst, Prod.snd, bodySP]
      bv_omega)
  have status := finished_status .sequential (emptyPrepared s) preparedBound
  refine ⟨empty_return_run s base code error aligned pc empty unplanned, returned, ?_, ?_, ?_⟩
  · rw [emptyReturned, (Memory.mem_eq_iff_read_mem_bytes_eq.mp (restored_memory _))]
    simpa only [resultRegister, sizeRegister] using length
  · rw [emptyReturned, (Memory.mem_eq_iff_read_mem_bytes_eq.mp (restored_memory _))]
    simpa only [resultRegister] using status
  · intro address outside
    rw [emptyReturned, restored_memory]
    have scratch := outside ((r (.GPR 31#5) s).toNat - 240, 240) (by simp [emptyWrites, Stack.envelope])
    have result := outside ((r (.GPR 0#5) s).toNat, 8) (by simp [emptyWrites])
    have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [emptyWrites])
    rw [finishFrame address]
    · exact emptyPrepared_frame s low address (fun span member => outside span (by simp [emptyWrites, member]))
    · intro span member
      simp only [finishWrites, resultRegister, emptyPrepared_sp,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simp only [Prod.fst, Prod.snd, bodySP] at scratch ⊢
        bv_omega
      · exact result
      · exact status

end SszArm.Codec.Emit.Parts
