import SszX86.MeasureBitsConstructorOwned

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- A prefix may write its actual allocations, a cursor only after an allocation,
and the real local activation. Publication is added only at its actual stores. -/
def PrefixWrites (s : MachineData) (calls : List (NatArithmetic.Outcome NatOperand))
    (a : BitVec 64) : Prop :=
  AllocationWrites calls a ∨
    (Allocated calls ∧ InSpan a (s.regs.rcx.toBitVec + 16) 8) ∨
    InSpan a (s.regs.rsp.toBitVec - 16) 232

theorem outside_of_not_span (a p : BitVec 64) (n : Nat) (safe : ¬ InSpan a p n) :
    Body.Outside a.toNat p.toNat n := by
  by_cases outside : Body.Outside a.toNat p.toNat n
  · exact outside
  · apply False.elim
    apply safe
    unfold Body.Outside at outside
    refine ⟨a.toNat - p.toNat, by omega, ?_⟩
    bv_omega

theorem body_local_span (s : MachineData) (off n : Nat) (within : off + n ≤ 216)
    (a : BitVec 64) (inside : InSpan a (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) n) :
    InSpan a (s.regs.rsp.toBitVec - 16) 232 := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨16 + off + i, by omega, ?_⟩
  simp only [BitVec.ofNat_add]
  bv_omega

theorem call_frame (s : MachineData) (ra : BitVec 64) :
    MemoryFrame s.dmem (callState s ra).dmem
      (fun a => InSpan a (s.regs.rsp.toBitVec - 16) 232) := by
  apply frame_mono _ _ _ _ (store_frame s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt)
  rintro a ⟨i, hi, rfl⟩
  refine ⟨8 + i, by omega, ?_⟩
  simp only [BitVec.ofNat_add]
  bv_omega

theorem constructor_result_mapped (s : MachineData) (address capacity used : BitVec 64)
    (wide : BitVec 128) : MappedExtension s.dmem (NatFromU128.resultMem s address capacity used wide) := by
  intro p n hm
  unfold NatFromU128.resultMem
  split
  · unfold NatFromU128.successMem
    repeat' first | exact hm | apply Large.mapped_store
  · split
    · unfold NatFromU128.errorMem
      repeat' first | exact hm | apply Large.mapped_store
    · unfold NatFromU128.successMem NatFromU128.commitMem
      repeat' first | exact hm | apply Large.mapped_store

/-- The accepted helper's resource-sensitive frame is translated to the caller's
same exact allocation trace; alignment bytes are never added to writable memory. -/
theorem constructor_frame (s before : MachineData) (after : MachineState)
    (address capacity current ra : BitVec 64) (wide : BitVec 128)
    (helperOwned : NatFromU128.Owned (callState before ra) wide address capacity current ra)
    (sp : before.regs.rsp = s.regs.rsp)
    (headerReg : before.regs.rcx = s.regs.rcx)
    (outReg : before.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 24)
    (post : NatFromU128.Post (callState before ra) wide address capacity current ra after) :
    MemoryFrame before.dmem after.1.dmem
      (PrefixWrites s [NatArithmetic.fromWide address.toNat capacity.toNat current.toNat wide]) := by
  let call := NatArithmetic.fromWide address.toNat capacity.toNat current.toNat wide
  intro a safe
  have helper : after.1.dmem.get? a = (callState before ra).dmem.get? a := by
    apply post.frame a
    · have outside : Body.Outside a.toNat before.regs.rdi.toNat 68 := by
        simpa only [UInt64.toNat_toBitVec] using
          outside_of_not_span a before.regs.rdi.toBitVec 68 (by
            intro inside
            apply safe
            exact Or.inr (Or.inr (body_local_span s 24 68 (by decide) a
              (by rw [outReg] at inside; with_unfolding_all exact inside))))
      change (match call.result with
        | .ok _ => Body.Outside a.toNat before.regs.rdi.toNat 16 ∧
            Body.Outside a.toNat (before.regs.rdi.toNat + 64) 4
        | .error _ => Body.Outside a.toNat before.regs.rdi.toNat 68)
      cases call.result with
      | error reason => exact outside
      | ok operand =>
        unfold Body.Outside at outside ⊢
        omega
    · intro r allocated
      have geometry := wide_allocation_geometry address.toNat capacity.toNat current.toNat wide r allocated
      constructor
      · have cursorNat : (s.regs.rcx.toBitVec + 16).toNat = s.regs.rcx.toNat + 16 := by
          have bound : s.regs.rcx.toNat + 24 ≤ 2^64 := by
            simpa only [callState, headerReg] using helperOwned.header_bound
          rw [← UInt64.toNat_toBitVec] at bound ⊢
          bv_omega
        simpa only [callState, headerReg, cursorNat] using
          outside_of_not_span a (s.regs.rcx.toBitVec + 16) 8 (by
            intro inside
            apply safe
            exact Or.inr (Or.inl ⟨⟨call, by simp only [List.mem_singleton, call], r, allocated⟩, inside⟩))
      · have pointerBound := (NatFromU128.reserve_geometry (callState before ra) wide
          address capacity current ra helperOwned r geometry.1).2.2.2.2.2.1
        have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
        rw [← pointerNat]
        apply outside_of_not_span
        intro inside
        apply safe
        left
        refine ⟨call, by simp only [List.mem_singleton, call], r, allocated, ?_⟩
        simpa only [call, geometry.2.1, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using inside
  exact helper.trans (call_frame before ra a (by
    intro inside
    exact safe (Or.inr (Or.inr (by simpa only [sp] using inside)))))

end SszX86.Measure.Bits
