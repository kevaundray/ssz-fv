import SszX86.DelimitedMath

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def bitScanState (s : MachineData) (counter : BitVec 64) (bits : BitVec 32)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec counter
      r11 := UInt64.ofBitVec (bits.setWidth 64)}
    status := flags}

/-- One literal INC / SHR32 / JNE iteration, with its undefined AF cut at the
block boundary rather than duplicated into the remainder of the loop. -/
theorem bit_scan_iteration (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (counter : BitVec 64) (bits : BitVec 32) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (bitScanState s (counter + 1) (bits >>> 1) flags,
        if bits >>> 1 = 0#32 then base + 80 else base + 72)) :
    Eventually (step e) P (bitScanState s counter bits flags, base + 72) := by
  have target := hc.targets ("delimited_u72", 72) (by decide)
  simp only [bitScanState]
  delimited_step 21 using hc
  delimited_step 22 using hc
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, Effects.All]
  constructor <;> delimited_step 23 using hc
  all_goals
    by_cases zero : bits >>> 1 = 0#32
    · have shifted : UInt64.ofBitVec (bits.setWidth 64) >>> 1 = 0 := by
        simpa using congrArg (fun value : BitVec 32 => UInt64.ofBitVec (value.setWidth 64)) zero
      simpa [zero, shifted, bitScanState, StatusFlags.from_result, Effects.All] using hp _
    · simpa [zero, target, bitScanState, StatusFlags.from_result, Effects.All] using hp _

/-- The loop counter starts at -1; exactly highestBit+1 increments execute.
No BSR correctness assumption is used: each iteration is the preceding ISA block. -/
theorem bit_scan_loop (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byte : UInt8) (nonzero : byte ≠ 0)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (bitScanState s (BitVec.ofNat 64 (Ssz.highestBit byte)) 0#32 flags, base + 80)) :
    ∀ remaining i, i + remaining = Ssz.highestBit byte → ∀ flags,
    Eventually (step e) P
      (bitScanState s (BitVec.ofNat 64 i - 1)
        (byte.toBitVec.setWidth 32 >>> i) flags, base + 72) := by
  have cert := highest_certificate byte nonzero
  have highest := SszNative.BitView.highestBit_lt byte
  intro remaining
  induction remaining with
  | zero =>
    intro i hi flags
    have eq : i = Ssz.highestBit byte := by omega
    subst i
    apply bit_scan_iteration e base hc
    intro fl
    rw [← BitVec.shiftRight_add, cert.1]
    simpa only [BitVec.sub_add_cancel, ↓reduceIte] using hp fl
  | succ remaining ih =>
    intro i hi flags
    apply bit_scan_iteration e base hc
    intro fl
    rw [← BitVec.shiftRight_add]
    have hn : byte.toBitVec.setWidth 32 >>> (i+1) ≠ 0#32 :=
      cert.2 ⟨i+1, by omega⟩ (by change i+1 ≤ Ssz.highestBit byte; omega)
    rw [ite_eq_right hn]
    have counter : BitVec.ofNat 64 i - 1 + 1 = BitVec.ofNat 64 (i+1) - 1 := by
      bv_omega
    rw [counter]
    exact ih (i+1) (by omega) fl

/-- MOV32 publishes the loop counter as the highest set-bit position. -/
theorem bit_scan_publish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with
          rbx := UInt64.ofBitVec ((s.regs.r10.toBitVec.setWidth 32).setWidth 64)}
        status := flags}, base + 89)) :
    Eventually (step e) P (s, base + 80) := by
  delimited_step 24 using hc
  delimited_step 25 using hc
  delimited_step 26 using hc
  exact hp _

end SszX86.Delimited
