import SszArm.HashFinalizePrepared

namespace SszArm.Hash.Finalize

/-- The delimiter is written before the sole one-/two-block branch is taken. -/
theorem prefix (s : ArmState) (base : BitVec 64) (value : StreamState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : FinalizeOwned s base value)
    (pc : read_pc s = base + finalizeOffset) :
    ∃ t, run 21 s = t ∧ Live s t ∧
      BufferAt s t (SszNative.HashStream.delimiterBuffer value) value.chaining value.byteLen ∧
      r (.GPR 0#5) t = BitVec.ofNat 64 (value.buffered.val + 1) ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 value.buffered.val ∧
      read_pc t = base + finalizeOffset +
        if value.buffered.val + 1 ≤ 56 then 168#64 else 84#64 := by
  have g := geometry owned
  have bounded := value.buffered.isLt
  let a := entryState s
  have activeA : Activation s a := entry_activation s base value error aligned owned
  have storedA : StateAt a (statePtr s) value := entry_stored s base value aligned owned
  have pcA : read_pc a = base + finalizeOffset + 16#64 := by
    rw [entry_pc s aligned, pc]
  have countA : r (.GPR 8#5) a = BitVec.ofNat 64 value.buffered.val :=
    (entry_count s aligned).trans storedA.buffered
  have alignedA := activeA.aligned aligned
  let b := guardState a
  have memoryB := guard_memory a alignedA
  have activeB : Activation s b := activeA.sameMemory g (guard_scalar a alignedA)
    (by intro reg lo hi h19 h20; simp) (guard_sp a alignedA) memoryB
  have storedB : StateAt b (statePtr s) value := by
    apply storedA.frame (writes := []) (fun _ _ => congrFun memoryB _) g.stateBound
    right; simp
  have pcB : read_pc b = base + finalizeOffset + 24#64 := by
    rw [guard_pc a alignedA (by rw [countA]; bv_omega), pcA]
    simp [BitVec.add_assoc]
  have countB : r (.GPR 8#5) b = BitVec.ofNat 64 value.buffered.val :=
    ((guard_scalar a alignedA).registers 8#5 (by simp)).trans countA
  have inputA : r (.GPR 1#5) a = statePtr s :=
    (entry_scalar s aligned).registers 1#5 (by decide)
  have outputA : r (.GPR 0#5) a = outputPtr s :=
    (entry_scalar s aligned).registers 0#5 (by decide)
  have inputB : r (.GPR 1#5) b = statePtr s :=
    ((guard_scalar a alignedA).registers 1#5 (by simp)).trans inputA
  have outputB : r (.GPR 0#5) b = outputPtr s :=
    ((guard_scalar a alignedA).registers 0#5 (by simp)).trans outputA
  have alignedB := activeB.aligned aligned
  let c := delimiterState b
  obtain ⟨activeC, bufferC, chainC, countC, lengthC⟩ :=
    delimiter_step s b base value owned aligned activeB storedB inputB countB
  have inputC : r (.GPR 1#5) c = statePtr s :=
    ((delimiter_scalar b alignedB).registers 1#5 (by decide)).trans inputB
  have outputC : r (.GPR 0#5) c = outputPtr s :=
    ((delimiter_scalar b alignedB).registers 0#5 (by decide)).trans outputB
  have pcC : read_pc c = base + finalizeOffset + 56#64 := by
    rw [delimiter_pc b alignedB, pcB]
    simp [BitVec.add_assoc]
  let t := prepareState c
  obtain ⟨liveT, storedT, countT, oldCountT⟩ :=
    prepare_step s c base value owned aligned activeC outputC inputC bufferC chainC countC lengthC
  have alignedC := activeC.aligned aligned
  have prepared : preparedCount c = BitVec.ofNat 64 (value.buffered.val + 1) := by
    simp only [preparedCount, inputC, countC, BitVec.ofNat_add]
    rfl
  refine ⟨t, ?_, liveT, storedT, countT, oldCountT, ?_⟩
  · rw [show 21 = 4 + (2 + (8 + 7)) by decide, run_plus,
      entry_run s base code error aligned (by simpa using pc), run_plus,
      guard_run a base (activeA.code code) activeA.error alignedA pcA, run_plus,
      delimiter_run b base (activeB.code code) activeB.error alignedB pcB,
      prepare_run c base (activeC.code code) activeC.error alignedC pcC]
  · rw [prepare_pc c alignedC, pcC, prepared]
    have exactCount : (BitVec.ofNat 64 (value.buffered.val + 1)).toNat =
        value.buffered.val + 1 := by bv_omega
    rw [exactCount]
    split <;> simp_all [BitVec.add_assoc]

end SszArm.Hash.Finalize
