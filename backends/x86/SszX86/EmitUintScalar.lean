import SszX86.EmitUintCertificates
import SszX86.EmitUintByteFacts
import SszX86.EmitUintMemory

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get put putF compare subFlags shift)

macro "uint_exec " certificate:ident " using " hc:term : tactic => `(tactic|
  (refine $certificate _ _ $hc _ 0 (by simp [Read]) (by simp [Writable]) _ ?_
   intro instructionFlags
   simp only [instruction, Instructions.next, UintCodec.Large.put, UintCodec.Large.putF,
     UintCodec.Large.get, UintCodec.Large.compare, test, store,
     Reg64s.set64, Reg64s.get64, UintCodec.Large.subFlags_cf, UintCodec.Large.subFlags_zf]))

macro "uint_write " certificate:ident " using " hc:term " mapped " hm:term : tactic => `(tactic|
  (refine $certificate _ _ $hc _ 0 (by simp [Read])
     (by simpa only [Writable, storeAddress, storeWidth, UintCodec.Large.get, Reg64s.get64,
       Nat.reduceEqDiff, or_true, true_or, or_false, false_or, true_implies,
       false_implies, ↓reduceIte] using $hm) _ ?_
   intro instructionFlags
   simp only [instruction, Instructions.next, UintCodec.Large.put, UintCodec.Large.putF,
     UintCodec.Large.get, UintCodec.Large.compare, test, store,
     Reg64s.set64, Reg64s.get64, UintCodec.Large.subFlags_cf, UintCodec.Large.subFlags_zf]))

/-- Exact written-length store and relative jump to the shared status store. -/
theorem length_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem s.regs.rbx.toBitVec 8 = some old)
    (next : Eventually (step e) P
      ({s with dmem := Mem.storeInt s.dmem s.regs.rbx.toBitVec 8 s.regs.rsi.toBitVec.toInt},
        base + 1593)) :
    Eventually (step e) P (s, base + 1147) := by
  uint_write at1147 using hc mapped hmap
  uint_exec at1150 using hc
  exact next

/-- Width zero does not read number limbs and does not touch the output at all. -/
theorem zero_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem s.regs.rbx.toBitVec 8 = some old)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rsi := 0}
        status := flags
        dmem := Mem.storeInt s.dmem s.regs.rbx.toBitVec 8 0}, base + 1593)) :
    Eventually (step e) P (s, base + 653) := by
  uint_exec at653 using hc
  uint_write at655 using hc mapped hmap
  uint_exec at658 using hc
  exact next _

/-- Derive the unsigned capacity guard from the logical fitting count. -/
theorem capacity_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (fits : s.regs.rsi.toNat ≤ s.regs.r9.toNat)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 592)) :
    Eventually (step e) P (s, base + 583) := by
  uint_exec at583 using hc
  uint_exec at586 using hc
  have condition : (!decide (s.regs.rsi.toNat < s.regs.r9.toNat) &&
      !(s.regs.rsi.toBitVec == s.regs.r9.toBitVec)) = false := by
    by_cases strict : s.regs.rsi.toNat < s.regs.r9.toNat
    · simp [strict]
    · have equal : s.regs.rsi.toBitVec = s.regs.r9.toBitVec := by
        apply BitVec.eq_of_toNat_eq
        simp only [UInt64.toNat_toBitVec]
        omega
      simp [equal]
  simp only [UInt64.toNat_toBitVec, condition, Bool.false_eq_true, ↓reduceIte]
  exact next _

/-- The nonzero width edge is proved, rather than supplied as a future guard. -/
theorem nonzero_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (nonzero : s.regs.rsi.toBitVec ≠ 0#64)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 597)) :
    Eventually (step e) P (s, base + 592) := by
  uint_exec at592 using hc
  uint_exec at595 using hc
  have condition : (s.regs.rsi.toBitVec == BitVec.zero 64) = false :=
    beq_eq_false_iff_ne.mpr nonzero
  simp only [StatusFlags.from_result, condition, Bool.false_eq_true, ↓reduceIte]
  exact next _

/-- Number representation is read from the original pair without normalizing or
trimming its physical limbs. Both zero and padded representations remain valid. -/
theorem number_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (pointerRead : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payloadRead : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rdi := UInt64.ofBitVec pointer, rdx := UInt64.ofBitVec payload}
        status := flags}, if pointer = 0#64 then base + 876 else base + 616)) :
    Eventually (step e) P (s, base + 597) := by
  refine at597 e base hc s pointer ?_ (by simp [Writable]) P ?_
  · simpa [Read, readAddress, UintCodec.Large.get, Reg64s.get64] using pointerRead
  intro firstFlags
  simp only [instruction, Instructions.next, UintCodec.Large.put, Reg64s.set64]
  refine at602 e base hc _ payload ?_ (by simp [Writable]) P ?_
  · simpa [Read, readAddress, UintCodec.Large.get, Reg64s.get64] using payloadRead
  intro secondFlags
  simp only [instruction, Instructions.next, UintCodec.Large.put, Reg64s.set64]
  uint_exec at607 using hc
  uint_exec at610 using hc
  by_cases zero : pointer = 0#64
  · simpa [StatusFlags.from_result, zero] using next _
  · simpa [StatusFlags.from_result, zero] using next _

end SszX86.Emit.Uint
