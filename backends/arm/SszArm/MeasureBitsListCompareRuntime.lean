import SszArm.MeasureBitsListCompare
import SszArm.MeasureHelpersCompareOwned
import SszArm.MeasureMemory

namespace SszArm.Measure.Bits.ListEntry

open UintCodec (widthLoad)
open SszNative (NatOperand)

structure ComparePost (s t : ArmState) (base : BitVec 64) (actual cap : NatOperand) : Prop where
  pc : read_pc t = if actual.value ≤ cap.value then base + 1852#64 else base + 1744#64
  program : t.program = s.program
  error : read_err t = .None
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 1#5, 2#5, 3#5, 8#5, 9#5, 10#5, 11#5, 12#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  actualAt : actual.At (widthLoad t)
  capAt : cap.At (widthLoad t)
  frame : Delimited.MemoryFrame (Helpers.loweringWrites s) s t

theorem compare_executes (s : ArmState) (base : BitVec 64) (actual cap : NatOperand)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1712#64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (actualPointer : r (.GPR 21#5) s = actual.pointer)
    (actualPayload : r (.GPR 24#5) s = actual.payload)
    (capPointer : r (.GPR 22#5) s = cap.pointer)
    (capPayload : r (.GPR 23#5) s = cap.payload)
    (actualAt : actual.At (widthLoad s)) (capAt : cap.At (widthLoad s))
    (actualOwned : NatDivision.OperandOwned (Helpers.loweringWrites s) actual)
    (capOwned : NatDivision.OperandOwned (Helpers.loweringWrites s) cap) :
    ∃ fuel t, run fuel s = t ∧ ComparePost s t base actual cap := by
  let p := compareReady s base
  have prepared : run 4 s = p := compare_setup_run s base code error pc
  have pProgram : p.program = s.program := by simp [p, compareReady, state_simp_rules]
  have pMemory : p.mem = s.mem := by simp [p, compareReady, state_simp_rules]
  have pSP : r (.GPR 31#5) p = r (.GPR 31#5) s := by simp [p, compareReady, state_simp_rules]
  have pError : read_err p = .None := by simpa [p, compareReady, state_simp_rules] using error
  have pAligned : CheckSPAlignment p := by
    simpa only [CheckSPAlignment, state_simp_rules, pSP] using aligned
  have pActual : actual.At (widthLoad p) := by rw [Emit.load_eq_of_mem_eq pMemory]; exact actualAt
  have pCap : cap.At (widthLoad p) := by rw [Emit.load_eq_of_mem_eq pMemory]; exact capAt
  have p0 : r (.GPR 0#5) p = actual.pointer := by simpa [p, compareReady, state_simp_rules] using actualPointer
  have p1 : r (.GPR 1#5) p = actual.payload := by simpa [p, compareReady, state_simp_rules] using actualPayload
  have p2 : r (.GPR 2#5) p = cap.pointer := by simpa [p, compareReady, state_simp_rules] using capPointer
  have p3 : r (.GPR 3#5) p = cap.payload := by simpa [p, compareReady, state_simp_rules] using capPayload
  obtain ⟨fuel, u, calledRun, native, returned, order, _, _⟩ :=
    Helpers.compare_correct p base actual.value cap.value (code.congr pProgram) pError pAligned
      (by simp [p, compareReady, state_simp_rules])
      (by rw [p0, p1]; exact SszNative.NatOperand.At.pair (widthLoad p) actual pActual)
      (by rw [p2, p3]; exact SszNative.NatOperand.At.pair (widthLoad p) cap pCap)
      (by
        rw [p0, p1]
        exact Helpers.compare_operand_owned p actual (by simpa only [pSP] using stackLow) pActual
          (by simpa only [Helpers.loweringWrites, pSP] using actualOwned))
      (by
        rw [p2, p3]
        exact Helpers.compare_operand_owned p cap (by simpa only [pSP] using stackLow) pCap
          (by simpa only [Helpers.loweringWrites, pSP] using capOwned))
  let t := compared (compare actual.value cap.value) u base
  have uProgram : u.program = s.program :=
    native.program.trans ((Helpers.called_program .compareCount p base).trans pProgram)
  have uError : read_err u = .None :=
    native.error.trans ((Helpers.called_error .compareCount p base).trans pError)
  have dispatched : run 3 u = t := compare_branch_run _ u base (code.congr uProgram) uError returned order
  have inputSP : r (.GPR 31#5) (Helpers.called .compareCount p base) = r (.GPR 31#5) s :=
    (Helpers.called_register _ _ _ _ (by decide)).trans pSP
  have frame : Delimited.MemoryFrame (Helpers.loweringWrites s) s t := by
    intro address outside
    have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [Helpers.loweringWrites])
    have last := native.memory address (by rw [inputSP]; dsimp at apart; omega)
    exact (congrFun (compared_memory _ u base) address).trans
      (last.trans ((congrFun (Helpers.called_memory .compareCount p base) address).trans
        (congrFun pMemory address)))
  refine ⟨4 + fuel + 3, t, by rw [run_plus, run_plus, prepared, calledRun, dispatched],
    ?_, (compared_program _ u base).trans uProgram, (compared_error _ u base).trans uError,
    ?_, ?_, NatDivision.operand_at_preserved frame actual actualAt actualOwned,
    NatDivision.operand_at_preserved frame cap capAt capOwned, frame⟩
  · have destination := compared_pc (compare actual.value cap.value) u base
    change read_pc (compared (compare actual.value cap.value) u base) = _
    by_cases within : actual.value ≤ cap.value
    · have notGreater : compare actual.value cap.value ≠ .gt := by
        intro greater
        have := Nat.compare_eq_gt.mp greater
        omega
      simpa only [within, notGreater, ↓reduceIte] using destination
    · have greater : compare actual.value cap.value = .gt := Nat.compare_eq_gt.mpr (by omega)
      simpa only [within, greater, ↓reduceIte] using destination
  · intro reg keep
    have notEight : reg ≠ 8#5 := by
      intro equal
      exact keep (by simp [equal])
    have notLink : reg ≠ 30#5 := by
      intro equal
      exact keep (by simp [equal])
    have calleeKeep : reg ∉ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5] := by
      intro member
      apply keep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    have setupKeep : r (.GPR reg) p = r (.GPR reg) s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at keep
      simp [p, compareReady, state_simp_rules, keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1]
    exact (compared_register _ u base reg notEight).trans
      ((native.registers reg calleeKeep).trans
        ((Helpers.called_register _ _ _ _ notLink).trans setupKeep))
  · intro reg
    have setup : r (.SFP reg) p = r (.SFP reg) s := by simp [p, compareReady, state_simp_rules]
    exact (compared_vector _ u base reg).trans
      ((native.vectors reg).trans ((Helpers.called_vectors .compareCount p base reg).trans setup))

end SszArm.Measure.Bits.ListEntry
