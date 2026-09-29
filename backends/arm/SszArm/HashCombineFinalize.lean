import SszArm.HashCombineCopy
import SszArm.HashCombineReturn
import SszArm.HashGeometry
import SszArm.HashFinalizeProofs

namespace SszArm.Hash.Combine

open Delimited (MemoryFrame)

def finalCallOps : List Op := [.p380, .p384, .p388]

@[irreducible] def finalCall (s : ArmState) : ArmState := block finalCallOps s

theorem finalCall_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 380#64) : run 3 s = finalCall s := by
  have follows : Follows base finalCallOps s := by
    change r .PC s = _ at pc
    simp [Follows, finalCallOps, Op.row, Op.effect, put, next,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [finalCall]
  exact runs finalCallOps s base code error follows

@[simp] theorem finalCall_program (s : ArmState) : (finalCall s).program = s.program := by
  simp only [finalCall, block_program]

@[simp] theorem finalCall_error (s : ArmState) : read_err (finalCall s) = read_err s := by
  simp only [finalCall, block_error]

@[simp] theorem finalCall_memory (s : ArmState) : (finalCall s).mem = s.mem := by
  simp [finalCall, finalCallOps, block, Op.effect, put, next, call, state_simp_rules]

@[simp] theorem finalCall_register (s : ArmState) (reg : BitVec 5)
    (different : reg ∉ [0#5, 1#5, 30#5]) : r (.GPR reg) (finalCall s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h30 : reg ≠ 30#5 := by simp_all
  simp [finalCall, finalCallOps, block, Op.effect, put, next, call,
    state_simp_rules, h0, h1, h30]

@[simp] theorem finalCall_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (finalCall s) = r (.SFP reg) s := by
  simp [finalCall, finalCallOps, block, Op.effect, put, next, call, state_simp_rules]

theorem finalCall_arguments (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 380#64) :
    read_pc (finalCall s) = base + finalizeOffset ∧
    r (.GPR 0#5) (finalCall s) = r (.GPR 19#5) s ∧
    r (.GPR 1#5) (finalCall s) = r (.GPR 31#5) s + 112#64 ∧
    r (.GPR 30#5) (finalCall s) = base + 392#64 := by
  change r .PC s = _ at pc
  simp [finalCall, finalCallOps, block, Op.effect, put, next, call,
    state_simp_rules, pc, finalizeOffset, BitVec.add_assoc]

/-- This suffix calls the proved finalizer theorem. There is no finalizer-run
hypothesis: CompressionCorrect is the only assumed helper semantics. -/
theorem finalize_return_correct (origin s : ArmState) (base : BitVec 64)
    (left right : ByteArray) (value : StreamState)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + 380#64) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : CombineOwned origin base left right)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) origin - 304#64)
    (output : r (.GPR 19#5) s = r (.GPR 0#5) origin)
    (state : StateAt s (r (.GPR 31#5) s + 112#64) value)
    (saved : Saved origin s) (program : s.program = origin.program)
    (prefixFrame : MemoryFrame (combineWrites origin) origin s)
    (semantic : SszNative.HashStream.finalize value = SszNative.HashStream.combine left right) :
    ∃ fuel, CombinePost origin (run fuel s) left right := by
  let q := finalCall s
  have arguments := finalCall_arguments s base pc
  have qSP : r (.GPR 31#5) q = r (.GPR 31#5) s := finalCall_register s 31#5 (by decide)
  have qOut : r (.GPR 0#5) q = r (.GPR 0#5) origin := arguments.2.1.trans output
  have qState : r (.GPR 1#5) q = r (.GPR 31#5) q + 112#64 := by
    rw [qSP]
    exact arguments.2.2.1
  have qSource : StateAt q (r (.GPR 1#5) q) value := by
    rw [arguments.2.2.1]
    exact stateAt_mem_eq (finalCall_memory s) state
  have qCode : CodeAt q base := code.of_program_eq (finalCall_program s)
  have qData : DataAt q base := by
    refine ⟨?_, ?_, data.initialBound, data.roundsBound⟩
    · simpa only [TableAt, BytesAt, q, finalCall_memory] using data.initial
    · simpa only [TableAt, BytesAt, q, finalCall_memory] using data.rounds
  have qAligned : CheckSPAlignment q := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, qSP] using aligned
  have qOwned := combine_finalize_owned origin q base left right value owned
    (qSP.trans sp) qOut qState qSource
  have low := owned.stackLow
  have physical : (r (.GPR 31#5) s).toNat + 304 ≤ 2^64 := by rw [sp]; bv_omega
  have qPhysical : (r (.GPR 31#5) q).toNat + 304 ≤ 2^64 := by rwa [qSP]
  have qSaved : Saved origin q := by
    apply saved.of_frame (writes := [])
    · intro address outside
      exact congrFun (finalCall_memory s) address
    · exact physical
    · right
      simp
    · exact qSP
    · intro reg lo hi
      exact finalCall_register s reg (by simp only [List.mem_cons, List.mem_singleton]; bv_omega)
    · intro reg lo hi
      rw [finalCall_vector]
  obtain ⟨fuel, finalized⟩ := SszArm.Hash.finalize_correct q base value qCode qData compression
    arguments.1 ((finalCall_error s).trans error) qAligned qOwned
  let t := run fuel q
  have tPC : read_pc t = base + 392#64 := finalized.returned.pc.trans arguments.2.2.2
  have tCode : CodeAt t base := qCode.of_program_eq finalized.returned.program
  have tAligned : CheckSPAlignment t := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, finalized.returned.sp] using qAligned
  have tSaved : Saved origin t := qSaved.of_frame finalized.frame qPhysical
    (combine_finalize_saved origin q base left right owned (qSP.trans sp) qOut qState)
    finalized.returned.sp
    (by intro reg lo hi; exact finalized.returned.registers reg (by omega) (by omega))
    finalized.returned.vectors
  have tProgram : t.program = origin.program :=
    finalized.returned.program.trans ((finalCall_program s).trans program)
  have tSP : r (.GPR 31#5) t + 304#64 = r (.GPR 31#5) origin := by
    rw [finalized.returned.sp, qSP, sp]
    bv_omega
  have resultReturned := epilogue_returned origin t tSaved tProgram finalized.returned.error tSP
  have helperFrame : MemoryFrame (combineWrites origin) q t :=
    frame_mono finalized.frame (combine_finalize_writes origin q base left right owned
      (qSP.trans sp) qOut qState)
  have prefixToCall : MemoryFrame (combineWrites origin) origin q := by
    intro address outside
    exact (congrFun (finalCall_memory s) address).trans (prefixFrame address outside)
  have finalFrame : MemoryFrame (combineWrites origin) origin (epilogue t) := by
    intro address outside
    exact (congrFun (epilogue_memory t) address).trans
      ((prefixToCall.trans helperFrame) address outside)
  have digest : BytesAt (epilogue t) (r (.GPR 0#5) origin)
      (SszNative.HashStream.combine left right) := by
    simpa only [BytesAt, epilogue_memory, qOut, semantic] using finalized.bytes
  refine ⟨3 + fuel + 7, ?_⟩
  rw [run_plus, run_plus, finalCall_run s base code error aligned pc,
    epilogue_run t base tCode finalized.returned.error tAligned tPC]
  exact ⟨resultReturned, digest, finalFrame,
    bytesAt_frame finalFrame owned.leftBound owned.leftOwned owned.left,
    bytesAt_frame finalFrame owned.rightBound owned.rightOwned owned.right⟩

theorem copy_finalize_return_correct (origin s : ArmState) (base : BitVec 64)
    (left right : ByteArray) (value : StreamState)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + 364#64) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : CombineOwned origin base left right)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) origin - 304#64)
    (output : r (.GPR 19#5) s = r (.GPR 0#5) origin)
    (state : StateAt s (r (.GPR 31#5) s) value)
    (saved : Saved origin s) (program : s.program = origin.program)
    (prefixFrame : MemoryFrame (combineWrites origin) origin s)
    (semantic : SszNative.HashStream.finalize value = SszNative.HashStream.combine left right) :
    ∃ fuel, CombinePost origin (run fuel s) left right := by
  have low := owned.stackLow
  have physical : (r (.GPR 31#5) s).toNat + 304 ≤ 2^64 := by rw [sp]; bv_omega
  let copyFuel := 3 + (Memcpy.fuel 112 + 1)
  let t := run copyFuel s
  have copied : StateCopyPost s t base value :=
    state_copy_correct s base value code error aligned pc (by omega) state
  have inclusion : ∀ span ∈ [((r (.GPR 31#5) s + 112#64).toNat, 112)],
      ∃ outer ∈ combineWrites origin,
        outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨stackSpan origin 496, by simp [combineWrites], ?_, ?_⟩
    all_goals simp only [stackSpan, sp]; bv_omega
  have tCode : CodeAt t base := code.of_program_eq copied.program
  have tData : DataAt t base := data.frame copied.frame
    (protected_writes_mono owned.initialOwned inclusion)
    (protected_writes_mono owned.roundsOwned inclusion)
  have tAligned : CheckSPAlignment t := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, copied.sp] using aligned
  have savedProtected : Delimited.Protected
      [((r (.GPR 31#5) s + 112#64).toNat, 112)] (r (.GPR 31#5) s + 224#64).toNat 80 := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    bv_omega
  have tSaved : Saved origin t := saved.of_frame copied.frame physical savedProtected copied.sp
    (by intro reg lo hi; exact copied.registers reg (by omega) (by omega)) copied.vectors
  have tState : StateAt t (r (.GPR 31#5) t + 112#64) value := by
    rw [copied.sp]
    exact copied.state
  have tFrame : MemoryFrame (combineWrites origin) origin t :=
    prefixFrame.trans (frame_mono copied.frame inclusion)
  obtain ⟨fuel, post⟩ := finalize_return_correct origin t base left right value
    tCode tData compression copied.pc copied.error tAligned owned (copied.sp.trans sp)
    ((copied.registers 19#5 (by decide) (by decide)).trans output)
    tState tSaved (copied.program.trans program) tFrame semantic
  refine ⟨copyFuel + fuel, ?_⟩
  rw [run_plus]
  exact post

end SszArm.Hash.Combine
