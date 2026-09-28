import SszX86.NatMulWordCount
import SszX86.DelimitedRetain

namespace SszX86.NatMulWord

/-- The scan's saved count is converted to the significant length before either
allocation or the scalar load. The impossible usize-overflow error is excluded
by the physical-span-derived bound passed by the scan composition. -/
theorem count_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : Nat) (positive : 0 < count) (bound : count+3 < 2^64)
    (saved : s.regs.r15.toBitVec = BitVec.ofNat 64 (count+3)) (P : MachineState → Prop)
    (small : count = 1 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r15 := UInt64.ofNat count}, status := flags}, base + 393))
    (large : 1 < count → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r15 := UInt64.ofNat count}, status := flags}, base + 195)) :
    Eventually (step e) P (s, base + 171) := by
  have target := hc.targets ("natMulWord_u393", 393) (by decide)
  have dec : s.regs.r15.toBitVec + 18446744073709551613#64 = BitVec.ofNat 64 count := by
    rw [saved]
    bv_omega
  have decReg : s.regs.r15 + 18446744073709551613 = (OfNat.ofNat count : UInt64) := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]
    exact dec
  natmulword_step 1:15 using hc
  natmulword_step 1:16 using hc
  natmulword_step 1:17 using hc
  by_cases one : count = 1
  · have eq : BitVec.ofNat 64 count = 1#64 := by simp [one]
    simpa [StatusFlags.from_result, dec, decReg, eq, target, Effects.All,
      UInt64.add_comm, BitVec.add_comm, Delimited.uint64_literal count] using small one _
  · have notone : BitVec.ofNat 64 count ≠ 1#64 := by bv_omega
    simp [StatusFlags.from_result, dec, decReg, notone, Effects.All, UInt64.add_comm, BitVec.add_comm]
    natmulword_step 1:18 using hc
    natmulword_step 1:19 using hc
    have notmax : BitVec.ofNat 64 count ≠ 18446744073709551615#64 := by bv_omega
    simpa [StatusFlags.from_result, dec, decReg, notmax, Effects.All,
      UInt64.add_comm, BitVec.add_comm, Delimited.uint64_literal count] using large (by omega) _

theorem small_word_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with r9 := UInt64.ofBitVec limb}}, base + 396)) :
    Eventually (step e) P (s, base + 393) := by
  natmulword_step 3:5 using hc
  natmulword_load loaded
  exact next

/-- All-zero Large representations still use the original physical word-zero
load when nonempty; the empty representation instead zeroes R9 explicitly. -/
theorem zero_count_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : s.regs.r9.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r9 := 0}, status := flags}, base + 516))
    (nonempty : s.regs.r9.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 393)) :
    Eventually (step e) P (s, base + 388) := by
  have target := hc.targets ("natMulWord_u513", 513) (by decide)
  natmulword_step 3:3 using hc
  constructor <;> natmulword_step 3:4 using hc
  all_goals
    by_cases zero : s.regs.r9.toBitVec = 0#64
    · simp [StatusFlags.from_result, zero, target, Effects.All]
      natmulword_step 4:7 using hc
      constructor <;> simpa using empty zero _
    · simpa [StatusFlags.from_result, zero, Effects.All] using nonempty zero _

end SszX86.NatMulWord
