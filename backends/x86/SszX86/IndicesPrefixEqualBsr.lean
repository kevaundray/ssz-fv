import SszX86.IndicesPrefixEqualSteps
import SszX86.MeasureUintBsrSteps
import SszSerializeMeasure

namespace SszX86.IndicesPrefixEqual
open UintCodec SszNative.Serialize

private def reserved (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16)}}

private def firstStore (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem s.regs.rsp.toBitVec 8 s.regs.r11.toBitVec.toInt}

private def secondStore (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8) 8 s.regs.r10.toBitVec.toInt}

private theorem lower_address (pointer : BitVec 64) :
    BitVec.ofInt 64 ((pointer.toInt + (-16)).bmod 18446744073709551616) =
      pointer - 16 := by
  have wrapped (value : Int) :
      BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
    simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
      (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))
  have minus : BitVec.ofInt 64 (-16) = -(16#64) := by decide
  simp only [wrapped, BitVec.ofInt_add, BitVec.ofInt_toInt, minus,
    ← BitVec.sub_eq_add_neg]

private theorem reserve_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (reserved s, base + 106)) :
    Eventually (step e) P (s, base + 101) := by
  indices_prefix_step 32 using hc
  simpa [reserved, lower_address, BitVec.sub_eq_add_neg] using next

private theorem first_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (firstStore s, base + 110)) :
    Eventually (step e) P (s, base + 106) := by
  indices_prefix_step 33 using hc
  apply Delimited.store_cps
  · exact Delimited.mapped_load_zero _ _ 16 8 mapped (by decide)
  simpa only [Effects.All, firstStore] using next

private theorem second_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (secondStore s, base + 115)) :
    Eventually (step e) P (s, base + 110) := by
  indices_prefix_step 34 using hc
  apply Delimited.store_cps
  · exact Large.mapped_load _ _ 16 8 8 mapped (by decide)
  simpa only [Effects.All, secondStore] using next

/-- These are the actual two writes at106 and110, not post-state assumptions. -/
theorem bsr_push_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (Measure.Uint.bsrPushed s, base + 115)) :
    Eventually (step e) P (s, base + 101) := by
  apply reserve_cps e base hc
  apply first_store_cps e base hc
  · exact mapped
  apply second_store_cps e base hc
  · exact Large.mapped_store _ _ _ _ _ _ mapped
  simpa only [reserved, firstStore, secondStore, Measure.Uint.bsrPushed,
    Measure.Uint.bsrMem, Delimited.bitSaveMem] using next

theorem bsr_start_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonzero : s.regs.rax.toBitVec ≠ 0#64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (Measure.Uint.bsrState s (-1#64) s.regs.rax.toBitVec flags, base + 130)) :
    Eventually (step e) P (s, base + 115) := by
  indices_prefix_step 35 using hc
  indices_prefix_step 36 using hc
  constructor <;> indices_prefix_step 37 using hc
  all_goals
    simp [nonzero, StatusFlags.from_result, Effects.All]
    indices_prefix_step 38 using hc
    simpa [Measure.Uint.bsrState] using next _

/-- One real INC64/SHR64/JNE iteration. Its undefined flags are hidden behind
this opaque boundary, preventing symbolic full-state growth in the induction. -/
theorem bsr_iteration_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (counter bits : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (Measure.Uint.bsrState s (counter + 1) (bits >>> 1) flags,
        if bits >>> 1 = 0#64 then base + 138 else base + 130)) :
    Eventually (step e) P (Measure.Uint.bsrState s counter bits flags, base + 130) := by
  have target := hc.targets ("indices_prefix_equal_u130", 130) (by decide)
  simp only [Measure.Uint.bsrState]
  indices_prefix_step 39 using hc
  indices_prefix_step 40 using hc
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, Effects.All]
  constructor <;> indices_prefix_step 41 using hc
  all_goals
    by_cases zero : bits >>> 1 = 0#64
    · have registerZero : UInt64.ofBitVec bits >>> 1 = UInt64.ofBitVec (0#64) := by
        change UInt64.ofBitVec bits >>> UInt64.ofNat 1 = UInt64.ofBitVec (0#64)
        rw [← UInt64.ofBitVec_shiftRight bits 1 (by decide), zero]
      simpa [registerZero, zero, Measure.Uint.bsrState, StatusFlags.from_result,
        Effects.All] using next _
    · simpa [zero, target, Measure.Uint.bsrState, StatusFlags.from_result,
        Effects.All] using next _

theorem bsr_loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (nonzero : limb ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (Measure.Uint.bsrState s (BitVec.ofNat 64 limb.toNat.log2) 0 flags, base + 138)) :
    ∀ remaining i, i + remaining = limb.toNat.log2 → ∀ flags,
      Eventually (step e) P
        (Measure.Uint.bsrState s (BitVec.ofNat 64 i - 1) (limb >>> i) flags,
          base + 130) := by
  have certificate := bsr_certificate limb nonzero
  intro remaining
  induction remaining with
  | zero =>
      intro i same flags
      have equal : i = limb.toNat.log2 := by omega
      subst i
      apply bsr_iteration_cps e base hc
      intro flags
      rw [← BitVec.shiftRight_add, certificate.1]
      simpa only [BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat, ↓reduceIte] using next flags
  | succ remaining ih =>
      intro i same flags
      apply bsr_iteration_cps e base hc
      intro flags
      rw [← BitVec.shiftRight_add]
      have nonempty : limb >>> (i + 1) ≠ 0#64 := by
        simpa only [BitVec.ofNat_eq_ofNat] using certificate.2 (i + 1) (by omega)
      rw [ite_eq_right nonempty]
      have counter : BitVec.ofNat 64 i - 1 + 1 = BitVec.ofNat 64 (i + 1) - 1 := by
        simp only [BitVec.ofNat_add, BitVec.sub_add_cancel, BitVec.add_sub_cancel]
      rw [counter]
      exact ih (i + 1) (by omega) flags

private def published (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := s.regs.r10}, status := flags}

theorem bsr_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (published s flags, base + 147)) :
    Eventually (step e) P (s, base + 138) := by
  indices_prefix_step 42 using hc
  indices_prefix_step 43 using hc
  indices_prefix_step 44 using hc
  simpa [published] using next _

theorem bsr_restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r10 r11 : BitVec 64)
    (lo : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (r11.toNat : Int))
    (hi : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (r10.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (Measure.Uint.bsrRestored s r10 r11, base + 161)) :
    Eventually (step e) P (s, base + 147) := by
  indices_prefix_step 45 using hc
  indices_prefix_load lo
  indices_prefix_step 46 using hc
  indices_prefix_load hi
  indices_prefix_step 47 using hc
  simpa [Measure.Uint.bsrRestored] using next

def bsrResult (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with dmem := Measure.Uint.bsrMem s,
    regs := {s.regs with rax := UInt64.ofNat s.regs.rax.toNat.log2}, status := flags}

/-- Complete execution of the first lowered BSR, including both original loads
that restore R10/R11 and the original stack-pointer restoration. -/
theorem bsr_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16) 16)
    (nonzero : s.regs.rax.toBitVec ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (bsrResult s flags, base + 161)) :
    Eventually (step e) P (s, base + 101) := by
  apply bsr_push_cps e base hc s mapped
  apply bsr_start_cps e base hc (Measure.Uint.bsrPushed s) nonzero
  intro initialFlags
  have finish : ∀ flags, Eventually (step e) P
      (Measure.Uint.bsrState (Measure.Uint.bsrPushed s)
        (BitVec.ofNat 64 s.regs.rax.toNat.log2) 0 flags, base + 138) := by
    intro loopFlags
    apply bsr_publish_cps e base hc
    intro publishFlags
    apply bsr_restore_cps e base hc _ s.regs.r10.toBitVec s.regs.r11.toBitVec
    · exact (Measure.Uint.bsr_saved_reads s).1
    · exact (Measure.Uint.bsr_saved_reads s).2
    · have result := next publishFlags
      simp [Measure.Uint.bsrRestored, published, Measure.Uint.bsrState,
        Measure.Uint.bsrPushed, bsrResult, BitVec.sub_add_cancel,
        UInt64.ofBitVec_toBitVec] at result ⊢
      with_unfolding_all exact result
  simpa [Measure.Uint.bsrPushed] using
    bsr_loop_cps e base hc (Measure.Uint.bsrPushed s) s.regs.rax.toBitVec nonzero P
      finish s.regs.rax.toNat.log2 0
      (by simp only [Nat.zero_add, UInt64.toNat_toBitVec]) initialFlags

end SszX86.IndicesPrefixEqual
