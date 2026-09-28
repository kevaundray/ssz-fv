import SszX86.MeasureBitsConstructorFrame

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem count_allocation_cursor (bits : Packed) (address capacity used : BitVec 64)
    (r : Arena.Reservation) (allocated : (countCall bits address capacity used).allocation = some r) :
    (countCall bits address capacity used).used = r.used ∧
      r.pointer + 16 = address.toNat + (countCall bits address capacity used).used := by
  have geometry := wide_allocation_geometry address.toNat capacity.toNat used.toNat bits.count r allocated
  by_cases small : bits.count.toNat < 2^64
  · simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged] at allocated
    cases allocated
  simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, geometry.1, NatArithmetic.committed]
  refine ⟨trivial, ?_⟩
  obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 geometry.1
  rw [shape]
  simp only [Arena.finish, Nat.reduceMul, Nat.add_assoc]

/-- The second allocation starts at or after the first committed cursor. Its
publication is local-stack-only, so every first-call limb survives either result. -/
theorem constructor_preserves_first_call (s before : MachineData) (after : MachineState)
    (desc : Desc) (bits : Packed) (buffer address capacity used current ra : BitVec 64)
    (wide : BitVec 128)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (currentEq : current.toNat = (countCall bits address capacity used).used)
    (helperOwned : NatFromU128.Owned (callState before ra) wide address capacity current ra)
    (headerReg : before.regs.rcx = s.regs.rcx)
    (outReg : before.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 24)
    (previous : CallsAt (widthLoad (callState before ra).dmem) [countCall bits address capacity used])
    (post : NatFromU128.Post (callState before ra) wide address capacity current ra after) :
    CallsAt (widthLoad after.1.dmem) [countCall bits address capacity used] := by
  intro call member r allocated
  have same : call = countCall bits address capacity used := by
    simpa only [List.mem_singleton] using member
  subst call
  have geometry := wide_allocation_geometry address.toNat capacity.toNat used.toNat bits.count r allocated
  have cursor := count_allocation_cursor bits address capacity used r allocated
  have firstWords := previous _ (by simp only [List.mem_singleton]) r allocated
  have freeStack := owned.freeStack
  have freeHeader := owned.freeHeader
  have arenaBound := owned.arenaBound
  have outputNat : before.regs.rdi.toNat = s.regs.rsp.toNat + 24 := by
    have stackBound := owned.stackBound
    rw [← UInt64.toNat_toBitVec, outReg, ← UInt64.toNat_toBitVec] at *
    bv_omega
  intro i
  have indexBound : i.val < 2 := by
    simpa only [countCall, geometry.2.1, List.length_cons, List.length_nil, Nat.reduceAdd] using i.isLt
  rw [post.memory]
  rw [NatFromU128.result_width_preserved (callState before ra) wide address capacity current ra
    helperOwned (r.pointer + 8 * i.val) 8]
  · exact firstWords i
  · omega
  · dsimp only [callState]
    rw [outputNat]
    unfold Body.Apart at freeStack ⊢
    have stackLow := owned.stackLow
    omega
  · dsimp only [callState]
    rw [headerReg]
    unfold Body.Apart at freeHeader ⊢
    omega
  · rw [currentEq]
    unfold Body.Apart
    omega

end SszX86.Measure.Bits
