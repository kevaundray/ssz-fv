import SszX86.NatDivisionCopyExec

namespace SszX86.NatDivision.Copy
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

abbrev odd (s : MachineData) : Prop := (get s .rax).setWidth 8 &&& 1#8 ≠ 0#8

def tailStore (s : MachineData) (value : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec value}
    dmem := Mem.storeInt s.dmem (get s .r14 + get s .r8 * 8#64) 8 value.toInt}

def finish (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbp := UInt64.ofBitVec (-get s .rbp)
      r15 := 0}
    status := flags}

/-- NEG, XOR and the real padding NOP reach the first reverse-division load. -/
theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (finish s flags, base + 768)) :
    Eventually (step e) P (s, base + 757) := by
  natdiv_step 204 using hc
  natdiv_step 205 using hc
  constructor <;> natdiv_step 206 using hc
  all_goals simpa [finish, get, Reg64s.get64] using next _

/-- Both odd-word source bounds outcomes perform the final destination store. -/
theorem tail_word_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (present : (get s .r8).toNat < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rsi + get s .r8 * 8#64) 8 = some (value.toNat : Int))
    (missing : ¬ (get s .r8).toNat < (get s .rdx).toNat → value = 0)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r14 + get s .r8 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (finish (tailStore s value) flags, base + 768)) :
    Eventually (step e) P (s, base + 740) := by
  have target751 := hc.targets ("natDivision_u751", 751) (by decide)
  simp only [get, Reg64s.get64, UInt64.toNat_toBitVec] at present missing
  natdiv_step 198 using hc
  natdiv_step 199 using hc
  by_cases inBounds : s.regs.r8.toNat < s.regs.rdx.toNat
  · simp [StatusFlags.from_result, Nat.not_le_of_gt inBounds]
    natdiv_step 200 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    natdiv_load (present inBounds)
    natdiv_step 201 using hc
    natdiv_step 203 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    apply Delimited.store_cps
    · exact hm
    simp only [Effects.All]
    apply finish_cps e base hc
    intro flags
    simpa [tailStore, finish, get, Reg64s.get64] using next flags
  · have branch : s.regs.rdx.toNat ≤ s.regs.r8.toNat := by omega
    simp [StatusFlags.from_result, branch, target751]
    have zero := missing inBounds
    subst value
    natdiv_step 202 using hc
    constructor <;> natdiv_step 203 using hc
    all_goals
      simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
      apply Delimited.store_cps
      · exact hm
      simp only [Effects.All]
      apply finish_cps e base hc
      intro flags
      simpa [tailStore, finish, get, Reg64s.get64] using next flags

/-- TEST/JE selects a complete odd-word copy or skips it for an even count. -/
theorem tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (present : odd s → (get s .r8).toNat < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rsi + get s .r8 * 8#64) 8 = some (value.toNat : Int))
    (missing : odd s → ¬ (get s .r8).toNat < (get s .rdx).toNat → value = 0)
    (hm : odd s → ∃ old, Mem.loadInt s.dmem (get s .r14 + get s .r8 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (finish (if odd s then tailStore s value else s) flags, base + 768)) :
    Eventually (step e) P (s, base + 736) := by
  have target757 := hc.targets ("natDivision_u757", 757) (by decide)
  natdiv_step 196 using hc
  constructor <;> natdiv_step 197 using hc
  all_goals
    by_cases isOdd : odd s
    · have nz : s.regs.rax.toBitVec.setWidth 8 &&& 1#8 ≠ 0#8 := by
        simpa only [odd, get, Reg64s.get64] using isOdd
      simp [StatusFlags.from_result, nz, Effects.All]
      apply tail_word_cps e base hc _ value
      · exact present isOdd
      · exact missing isOdd
      · exact hm isOdd
      intro flags
      simpa [finish, tailStore, isOdd] using next flags
    · have zero : s.regs.rax.toBitVec.setWidth 8 &&& 1#8 = 0#8 := by
        by_cases h : s.regs.rax.toBitVec.setWidth 8 &&& 1#8 = 0#8
        · exact h
        · exact False.elim (isOdd h)
      simp [StatusFlags.from_result, zero, target757, Effects.All]
      apply finish_cps e base hc
      intro flags
      simpa [finish, isOdd] using next flags

/-- The pair-loop exit advances its last pair index to the odd-tail index. -/
def exitPair (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := UInt64.ofBitVec (get s .r8 + 2#64)
      r14 := UInt64.ofBitVec (get s .r14 + get s .rdi)}
    status := flags}

theorem exit_pair_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (exitPair s flags, base + 736)) :
    Eventually (step e) P (s, base + 729) := by
  natdiv_step 194 using hc
  natdiv_step 195 using hc
  simpa [exitPair, get, Reg64s.get64, UInt64.add_comm] using next _

end SszX86.NatDivision.Copy
