import SszX86.NatMulWordWorkMemory
import SszX86.NatMulWordReturn
import SszX86.NatFromU128Resources

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- A memory-only adapter for the already checked from_u128 publication proof.
Its RSP is the original caller slot; it is never used to execute another image. -/
def wideBase (s : MachineData) (wide : BitVec 128) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec (wide.setWidth 64)
      rdx := UInt64.ofBitVec ((wide >>> 64).setWidth 64)
      rcx := s.regs.r8}
    dmem := pushedMem s}

theorem wide_owned (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (wide : BitVec 128) : NatFromU128.Owned (wideBase s wide) wide address capacity used ra := by
  have header := pushed_header s operand factor address capacity used ra owned
  have outputMapped := Delimited.Reservation.mapped_subrange (pushedMem s) s.regs.rdi.toBitVec
    72 0 68 (pushed_mapped s _ _ owned.output_mapped) (by decide)
  have outputBound := owned.output_bound
  have outputHeader := owned.header_output
  have outputReturn := owned.output_return
  have freeOutput := owned.arena_output
  refine ⟨rfl, rfl, ?_, owned.arena_bound, owned.arena_nonzero,
    pushed_mapped s _ _ owned.free_mapped, owned.header_bound, ?_, ?_, owned.return_bound,
    ?_, ?_, ?_, ?_, owned.arena_header, owned.arena_return, owned.cursor_return⟩
  · exact ⟨header.1, header.2.1, header.2.2⟩
  · change s.regs.rdi.toNat + 68 ≤ 2^64
    omega
  · simpa only [wideBase, BitVec.add_zero] using outputMapped
  · exact (pushed_model_frame s
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)
      owned.stack_low).return_slot owned
  · change Body.Apart s.regs.rdi.toNat 68 s.regs.r8.toNat 24
    unfold Body.Apart at outputHeader ⊢
    omega
  · change Body.Apart s.regs.rdi.toNat 68 s.regs.rsp.toNat 8
    unfold Body.Apart at outputReturn ⊢
    omega
  · change Body.Apart (address.toNat+used.toNat) (capacity.toNat-used.toNat) s.regs.rdi.toNat 68
    unfold Body.Apart at freeOutput ⊢
    omega

def smallResultMem (s : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) : DataMem :=
  NatFromU128.resultMem (wideBase s (SszNative.NatMul.wordProduct operand factor))
    address capacity used (SszNative.NatMul.wordProduct operand factor)

private theorem fromWide_written_length (base capacity used : Nat) (wide : BitVec 128)
    (r : Arena.Reservation) (allocated : (NatArithmetic.fromWide base capacity used wide).allocation = some r) :
    (NatArithmetic.fromWide base capacity used wide).written.length = 2 := by
  by_cases fits : wide.toNat < 2^64
  · simp only [NatArithmetic.fromWide, fits, ↓reduceIte, NatArithmetic.unchanged] at allocated
    cases allocated
  · cases reserved : Arena.reserve base capacity used 2 with
    | none =>
      simp only [NatArithmetic.fromWide, fits, ↓reduceIte, reserved, NatArithmetic.unchanged] at allocated
      cases allocated
    | some actual =>
      simp only [NatArithmetic.fromWide, fits, ↓reduceIte, reserved, NatArithmetic.committed, List.length_cons,
        List.length_nil]

theorem small_result_work (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1) :
    WorkFrame s (smallResultMem s operand factor address capacity used)
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat) := by
  have physical := wide_owned s operand factor address capacity used ra owned
    (SszNative.NatMul.wordProduct operand factor)
  have frame := NatFromU128.result_frame _ _ address capacity used ra physical
  rw [SszNative.NatMul.runWord_small operand factor _ _ _ nonzero notone small]
  intro a output locals scratch
  apply frame a output
  intro r allocated
  have away := scratch r allocated
  have length := fromWide_written_length address.toNat capacity.toNat used.toNat
    (SszNative.NatMul.wordProduct operand factor) r allocated
  simpa only [length, Nat.reduceMul, wideBase] using away

/-- On all scalar branches, the exact output and allocator observations are
those of the checked fromWide model, including unchanged failure memory. -/
theorem small_result_finished (s t : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (memory : t.dmem = smallResultMem s operand factor address capacity used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 64) (simd : t.zmms = s.zmms) :
    Finished s operand factor address capacity used t := by
  have physical := wide_owned s operand factor address capacity used ra owned
    (SszNative.NatMul.wordProduct operand factor)
  have model := SszNative.NatMul.runWord_small operand factor address.toNat capacity.toNat used.toNat
    nonzero notone small
  have work := small_result_work s operand factor address capacity used ra owned nonzero notone small
  have exactFrame := work.to_frame owned.stack_low
  have saved := work.saved owned
  refine ⟨?_, ?_, ?_, ?_, sp, ?_, simd⟩
  · rw [memory, model]
    exact NatFromU128.result_observed _ _ address capacity used ra physical
  · intro r allocated
    have stored := NatFromU128.result_written _ _ address capacity used ra physical r
      (by simpa only [model] using allocated)
    rw [memory, model]
    have pointerNat := allocated_pointer_nat s operand factor address capacity used ra owned r allocated
    simpa only [pointerNat, smallResultMem, NatFromU128.outcome] using stored.2.2.2
  · rw [memory]
    exact exactFrame
  · rw [memory, model]
    exact NatFromU128.result_cursor _ _ address capacity used ra physical
  · rw [memory, sp]
    have same : s.regs.rsp.toBitVec - 64 + 16 = s.regs.rsp.toBitVec - 48 := by bv_omega
    rw [same]
    exact saved

end SszX86.NatMulWord
