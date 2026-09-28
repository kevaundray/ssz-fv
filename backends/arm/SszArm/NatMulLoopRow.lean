import SszArm.NatMulLoopLeft
import SszArm.NatMulLoopInner
import SszArm.NatMulLoopCarry

namespace SszArm.NatMul

open SszNative (LimbMul)
open NatCompare (Words)
open Delimited (Protected MemoryFrame)

/-- One row: raw Nat::word, the real inner initialization, arbitrary many
actual columns, carry overwrite, and the original row backedge. -/
theorem loop_row_run (s : ArmState) (base sp source dst : BitVec 64)
    (left row : Nat) (leftRaw right doneWords buffer : List (BitVec 64))
    (space : LoopSpace sp dst (left + right.length)) (rowBound : row < left)
    (rightPositive : 0 < right.length)
    (prefixLength : doneWords.length = row) (bufferLength : row + buffer.length = left + right.length)
    (sourcePhysical : source.toNat + 8 * right.length ≤ 2^64)
    (sourceOwned : Protected (loopWrites sp dst (left + right.length)) source.toNat (8 * right.length))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 600#64) (spAt : r (.GPR 31#5) s = sp)
    (sourceAt : r (.GPR 8#5) s = source)
    (rowPointer : r (.GPR 11#5) s = dst + BitVec.ofNat 64 (8 * row))
    (rowAt : r (.GPR 12#5) s = BitVec.ofNat 64 row)
    (countAt : r (.GPR 19#5) s = BitVec.ofNat 64 (left + right.length))
    (dstAt : r (.GPR 20#5) s = dst) (leftAt : r (.GPR 21#5) s = BitVec.ofNat 64 left)
    (rightAt : r (.GPR 22#5) s = BitVec.ofNat 64 right.length)
    (widthAt : r (.GPR 25#5) s = BitVec.ofNat 64 right.length)
    (operand : NatCompare.Operand s (r (.GPR 9#5) s) (r (.GPR 10#5) s) leftRaw)
    (sourceWords : Words s source right) (bufferWords : Words s dst (currentWords doneWords buffer)) :
    ∃ fuel t, run fuel s = t ∧ LoopStable loopOuterChanged s t ∧
      MemoryFrame (loopWrites sp dst (left + right.length)) s t ∧
      read_pc t = base + (if row + 1 = left then 1012#64 else 600#64) ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 (row + 1) ∧
      r (.GPR 11#5) t = dst + BitVec.ofNat 64 (8 * (row + 1)) ∧
      Words t dst (doneWords ++ LimbMul.nativeRow (leftRaw[row]?.getD 0#64) right buffer) := by
  let factor := leftRaw[row]?.getD 0#64
  have countBound : left + right.length < 2^64 := by have := space.physical; omega
  obtain ⟨choiceFuel, u, runU, uf, um, up, factorAt⟩ := loop_left_run s base leftRaw row
    code error aligned pc (by rw [spAt]; exact space.stack) (by omega) rowAt operand
  have sourceOwnedSmall : Protected [(sp.toNat - 48, 48)] source.toNat (8 * right.length) := by
    rcases sourceOwned with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      apply separate span
      simp only [List.mem_singleton] at member
      subst span
      simp [loopWrites]
  have outputOwnedSmall : Protected [(sp.toNat - 48, 48)] dst.toNat (8 * (doneWords ++ buffer).length) := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    have := space.apart
    have := space.stack
    simp only [List.length_append, prefixLength, bufferLength, Prod.fst, Prod.snd]
    omega
  have um' : MemoryFrame [(sp.toNat - 48, 48)] s u := by simpa only [spAt] using um
  have uBuffer := words_preserve um' (by simp only [List.length_append, prefixLength, bufferLength]; exact space.physical)
    outputOwnedSmall bufferWords
  have uSource := words_preserve um' sourcePhysical sourceOwnedSmall sourceWords
  let v := loopRowInit base u
  have runV : run 4 u = v := loop_row_init_run u base (uf.code code) (uf.error.trans error)
    (uf.aligned aligned) up
  have vf : LoopStable loopOuterChanged u v := by
    constructor
    · simp [v, loopRowInit]
    · simp [v, loopRowInit]
    · simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules]
    · intro reg different
      simp_all [v, loopRowInit, block, Op.effect, put, next, state_simp_rules]
    · intro reg
      simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules]
  have allV : LoopStable loopOuterChanged s v := (uf.weaken (by simp)).trans vf
  have vm : v.mem = u.mem := by simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules]
  have vr (reg : BitVec 5) (different : reg ∉ [13#5, 15#5, 16#5, 17#5]) :
      r (.GPR reg) v = r (.GPR reg) u := by
    simp_all [v, loopRowInit, block, Op.effect, put, next, state_simp_rules]
  have vRow : r (.GPR 12#5) v = BitVec.ofNat 64 row :=
    (vr _ (by decide)).trans ((uf.registers _ (by decide)).trans rowAt)
  have vPointer : r (.GPR 11#5) v = dst + BitVec.ofNat 64 (8 * row) :=
    (vr _ (by decide)).trans ((uf.registers _ (by decide)).trans rowPointer)
  have v13 : r (.GPR 13#5) v = BitVec.ofNat 64 (row + 1) := by
    simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules,
      uf.registers 12#5 (by decide), rowAt, BitVec.ofNat_add]
  have vWords : Words v dst (currentWords doneWords buffer) := by
    intro i; rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp vm]; exact uBuffer i
  have vSource : Words v source right := by
    intro i; rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp vm]; exact uSource i
  obtain ⟨innerFuel, w, runW, wf, wm, wp, wColumn, wCarry, wZero, wWords⟩ :=
    loop_inner_runs base sp source dst left row right factor space rowBound sourcePhysical sourceOwned
      right.length rightPositive 0 doneWords buffer 0 v (by omega) (by omega) (by omega)
      (by omega) (by decide) (allV.code code) (allV.error.trans error) (allV.aligned aligned)
      (by simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules, up, BitVec.add_assoc])
      (allV.sp.trans spAt)
      ((allV.registers _ (by decide)).trans sourceAt) vPointer vRow
      (by simpa only [vr 14#5 (by decide), factor] using factorAt)
      (by simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules])
      (by simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules])
      (by simp [v, loopRowInit, block, Op.effect, put, next, state_simp_rules])
      ((allV.registers _ (by decide)).trans countAt)
      ((allV.registers _ (by decide)).trans dstAt)
      ((allV.registers _ (by decide)).trans widthAt) vSource vWords
  simp only [List.drop_zero] at wCarry wWords
  have allW := allV.trans (wf.weaken (by intro reg member; simp_all))
  have wRow := (wf.registers 12#5 (by decide)).trans vRow
  have w13 := (wf.registers 13#5 (by decide)).trans v13
  have wPointer := (wf.registers 11#5 (by decide)).trans vPointer
  obtain ⟨t, runT, tf, tm, tp, tRow, tPointer, stored⟩ := loop_row_finish_run w base dst
    (BitVec.ofNat 64 (LimbMul.inner right.length factor right buffer 0).2)
    left right.length row (allW.code code) (allW.error.trans error) (allW.aligned aligned) wp
    (by rw [allW.sp, spAt]; exact space.stack) space.physical
    (by rw [allW.sp, spAt]; exact space.apart) rowBound wRow w13
    ((allW.registers _ (by decide)).trans countAt)
    ((allW.registers _ (by decide)).trans dstAt)
    ((allW.registers _ (by decide)).trans leftAt)
    ((allW.registers _ (by decide)).trans rightAt) wPointer wCarry
  have cell : MemoryFrame [(sp.toNat - 48, 48),
      ((dst + BitVec.ofNat 64 (8 * (row + right.length))).toNat, 8)] w t := by
    simpa only [allW.sp, spAt] using tm
  have carryFrame := loopFrame_of_cell space (row + right.length) (by omega) cell
  have firstFrame : MemoryFrame (loopWrites sp dst (left + right.length)) s v := by
    intro a outside
    rw [vm]
    apply um' a
    intro span member
    apply outside span
    simp only [List.mem_singleton] at member
    subst span
    simp [loopWrites]
  refine ⟨choiceFuel + 4 + innerFuel + 15, t, ?_, allW.trans tf,
    (firstFrame.trans wm).trans carryFrame, tp, tRow, tPointer, ?_⟩
  · rw [run_plus, run_plus, run_plus, runU, runV, runW, runT]
  · let emitted := (LimbMul.inner right.length factor right buffer 0).1
    have emittedLength : emitted.length = right.length := LimbMul.inner_length _ _ _ _ _
    have suffixPositive : 0 < (buffer.drop right.length).length := by
      simp only [List.length_drop]
      omega
    cases dropEq : buffer.drop right.length with
    | nil => simp [dropEq] at suffixPositive
    | cons old tail =>
      have sized : LoopSpace sp dst ((doneWords ++ emitted) ++ old :: tail).length := by
        have droppedLength := congrArg List.length dropEq
        simp only [List.length_drop, List.length_cons] at droppedLength
        convert space using 1
        simp only [List.length_append, List.length_cons, emittedLength, prefixLength]
        omega
      have observed : Words w dst ((doneWords ++ emitted) ++ old :: tail) := by
        simpa only [emitted, dropEq] using wWords
      have cell' : MemoryFrame [(sp.toNat - 48, 48),
          ((dst + BitVec.ofNat 64 (8 * (doneWords ++ emitted).length)).toNat, 8)] w t := by
        simpa only [List.length_append, prefixLength, emittedLength] using cell
      have stored' : read_mem_bytes 8 (dst + BitVec.ofNat 64 (8 * (doneWords ++ emitted).length)) t =
          BitVec.ofNat 64 (LimbMul.inner right.length factor right buffer 0).2 := by
        simpa only [List.length_append, prefixLength, emittedLength] using stored
      have updated := words_replace_of_frame (doneWords ++ emitted) tail sized observed cell' stored'
      have tailEq : buffer.drop (right.length + 1) = tail := by
        rw [← List.tail_drop, dropEq]
        rfl
      simpa only [LimbMul.nativeRow, LimbMul.row, factor, ← List.append_assoc, tailEq, emitted]
        using updated

end SszArm.NatMul
