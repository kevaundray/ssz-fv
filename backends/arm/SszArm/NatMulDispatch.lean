import SszArm.NatMulDispatchRight

namespace SszArm.NatMul

open SszNative.Limbs

/-- Main multiplication's complete original dispatch, starting immediately
after its separately proved prologue. Raw operands are not canonicalized:
empty Large and all redundant high limbs execute their actual scans. -/
theorem dispatch (s : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64)
    (hl : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left)
    (hr : NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right) :
    ∃ fuel t, run fuel s = t ∧ DispatchFrame s t ∧ DispatchExit s t base left right := by
  obtain ⟨fuel, u, hu, huf, stage⟩ := left_dispatch s base left hc he ha hp hl
  by_cases small : r (.GPR 3#5) s = 0#64
  · have representation := hr.small small
    have count : sigWords right = if r (.GPR 4#5) s = 0#64 then 0 else 1 := by
      rw [representation]
      simp [sigWords, significantCount]
    have low : right[0]?.getD 0#64 = r (.GPR 4#5) s := by simp [representation]
    have pc : read_pc u = base +
        (if sigWords left = 0 ∨ r (.GPR 4#5) s = 0#64 then 264#64 else 228#64) := by
      simpa [LeftDispatch, small] using stage
    refine ⟨fuel, u, hu, huf.dispatch, ?_⟩
    by_cases zero : sigWords left = 0 <;> by_cases rzero : r (.GPR 4#5) s = 0#64 <;>
      simp [DispatchExit, count, zero, rzero, pc, RawArgs, low,
        huf.registers 1#5 (by decide), huf.registers 2#5 (by decide),
        huf.registers 3#5 (by decide), huf.registers 4#5 (by decide)]
  · obtain ⟨hu21, hu8, hup⟩ : r (.GPR 21#5) u = BitVec.ofNat 64 (sigWords left) ∧
        r (.GPR 8#5) u = r (.GPR 2#5) s ∧ read_pc u = base + 160#64 := by
      simpa [LeftDispatch, small] using stage
    have hlu : NatCompare.Operand u (r (.GPR 1#5) u) (r (.GPR 2#5) u) left := by
      simpa only [huf.registers 1#5 (by decide), huf.registers 2#5 (by decide)] using
        huf.operand _ _ _ hl
    have hru : NatCompare.Operand u (r (.GPR 3#5) u) (r (.GPR 4#5) u) right := by
      simpa only [huf.registers 3#5 (by decide), huf.registers 4#5 (by decide)] using
        huf.operand _ _ _ hr
    have largeu : r (.GPR 3#5) u ≠ 0#64 := by
      simpa only [huf.registers 3#5 (by decide)] using small
    have rawu : r (.GPR 8#5) u = r (.GPR 2#5) u := by
      rw [hu8, huf.registers 2#5 (by decide)]
    obtain ⟨rest, t, ht, htf, exit⟩ := right_dispatch u base left right
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hlu hru largeu hu21 rawu
    refine ⟨fuel + rest, t, ?_, huf.dispatch.trans htf, DispatchExit.prepend huf exit⟩
    rw [run_plus, hu, ht]

/-- Integration form explicitly retains both complete source representations
at their original pointers, even after the helper argument swap. -/
theorem dispatch_operands (s : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64)
    (hl : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left)
    (hr : NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right) :
    ∃ fuel t, run fuel s = t ∧ DispatchFrame s t ∧ DispatchExit s t base left right ∧
      NatCompare.Operand t (r (.GPR 1#5) s) (r (.GPR 2#5) s) left ∧
      NatCompare.Operand t (r (.GPR 3#5) s) (r (.GPR 4#5) s) right := by
  obtain ⟨fuel, t, execution, frame, exit⟩ := dispatch s base left right hc he ha hp hl hr
  exact ⟨fuel, t, execution, frame, exit, frame.operand _ _ _ hl, frame.operand _ _ _ hr⟩

end SszArm.NatMul
