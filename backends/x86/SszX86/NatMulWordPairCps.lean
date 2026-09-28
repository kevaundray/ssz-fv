import SszX86.NatMulWordPairState

namespace SszX86.NatMulWord
open UintCodec

/-- One complete original two-limb iteration. The second read names the exact
first-store memory, so consumers establish it from input/output separation;
neither scratch limb is assumed initialized. Arithmetic is LimbMul.step. -/
theorem pair_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (first second : BitVec 64)
    (firstLoaded : s.regs.rax.toNat < s.regs.r9.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec * 8#64) 8 =
        some (first.toNat : Int))
    (firstAbsent : s.regs.r9.toNat ≤ s.regs.rax.toNat → first = 0#64)
    (secondLoaded : (s.regs.rax.toBitVec + 1).toNat < s.regs.r9.toNat →
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstStep s first).1.toInt)
        (s.regs.rsi.toBitVec + s.regs.rax.toBitVec * 8#64 + 8#64) 8 = some (second.toNat : Int))
    (secondAbsent : s.regs.r9.toNat ≤ (s.regs.rax.toBitVec + 1).toNat → second = 0#64)
    (firstMapped : Large.Mapped s.dmem (firstAddress s) 8)
    (secondMapped : Large.Mapped s.dmem (secondAddress s) 8)
    (P : MachineState → Prop)
    (done : s.regs.rax.toBitVec + 1 = s.regs.r12.toBitVec → ∀ flags,
      Eventually (step e) P (unrolledState s first second flags, base + 702))
    (more : s.regs.rax.toBitVec + 1 ≠ s.regs.r12.toBitVec → ∀ flags,
      Eventually (step e) P (unrolledState s first second flags, base + 466)) :
    Eventually (step e) P (s, base + 466) := by
  apply first_fetch_cps e base hc s first firstLoaded firstAbsent
  intro fetchFlags
  apply first_product_cps e base hc
  intro mulFlags
  apply first_carry_cps e base hc
  intro firstFlags
  rw [first_product_bridge]
  apply first_store_cps e base hc
  · apply Delimited.mapped_load_zero (capacity := 8) (byteCount := 8)
    · exact firstMapped
    · decide
  rw [first_store_bridge]
  apply second_fetch_cps e base hc _ second
  · exact secondLoaded
  · exact secondAbsent
  intro secondFetchFlags
  apply second_product_cps e base hc
  intro secondMulFlags
  apply second_carry_cps e base hc
  intro secondFlags
  rw [second_product_bridge]
  apply second_store_cps e base hc
  · apply Delimited.mapped_load_zero (capacity := 8) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ secondMapped
    · decide
  rw [second_store_bridge]
  apply loop_advance_cps e base hc
  · intro last flags
    have last' : s.regs.rax.toBitVec + 1 = s.regs.r12.toBitVec := last
    simpa only [unrolledState, secondProducedState] using done last' flags
  · intro last flags
    have last' : s.regs.rax.toBitVec + 1 ≠ s.regs.r12.toBitVec := last
    simpa only [unrolledState, secondProducedState] using more last' flags

end SszX86.NatMulWord
