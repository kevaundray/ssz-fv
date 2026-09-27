import SszX86.NatDivisionCopyMemory

namespace SszX86.NatDivision.Copy
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

abbrev get (s : MachineData) (r : Reg64) : BitVec 64 := s.regs.get64 r

def firstAddress (s : MachineData) : BitVec 64 := get s .r9 + get s .r10 * 8#64 - 8#64

def first (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := s.regs.r10
      r10 := UInt64.ofBitVec (get s .r10 + 1#64)}
    dmem := Mem.storeInt s.dmem (firstAddress s) 8 value.toInt
    status := flags}

/-- Both first-word bounds-check paths execute a physical eight-byte store. -/
theorem first_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (present : (get s .r10).toNat < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rsi + get s .r10 * 8#64) 8 = some (value.toNat : Int))
    (missing : ¬ (get s .r10).toNat < (get s .rdx).toNat → value = 0)
    (hm : ∃ old, Mem.loadInt s.dmem (firstAddress s) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (first s value flags, if (get s .r10 + 1#64).toNat < (get s .rdx).toNat
        then base + 652 else base + 714)) :
    Eventually (step e) P (s, base + 669) := by
  have target697 := hc.targets ("natDivision_u697", 697) (by decide)
  have target652 := hc.targets ("natDivision_u652", 652) (by decide)
  simp only [get, Reg64s.get64, UInt64.toNat_toBitVec] at present missing
  have incrementNat :
      ((s.regs.r10.toBitVec.toInt + 1) % 18446744073709551616).toNat =
        (s.regs.r10.toNat + 1) % 18446744073709551616 := by
    have cast : BitVec.ofInt 64 (s.regs.r10.toBitVec.toInt + 1) =
        s.regs.r10.toBitVec + 1#64 := by
      rw [BitVec.ofInt_add, BitVec.ofInt_toInt]
      rfl
    have natural := congrArg BitVec.toNat cast
    simp only [BitVec.toNat_ofInt, BitVec.toNat_add, UInt64.toNat_toBitVec,
      show (1#64).toNat = 1 by rfl] at natural
    change ((s.regs.r10.toBitVec.toInt + 1) % (18446744073709551616 : Int)).toNat =
      (s.regs.r10.toNat + 1) % (18446744073709551616 : Nat) at natural
    exact natural
  natdiv_step 175 using hc
  natdiv_step 176 using hc
  natdiv_step 177 using hc
  by_cases presentWord : s.regs.r10.toNat < s.regs.rdx.toNat
  · simp [StatusFlags.from_result, Nat.not_le_of_gt presentWord]
    natdiv_step 178 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    natdiv_load (present presentWord)
    natdiv_step 179 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    apply Delimited.store_cps
    · simpa [firstAddress, get, Reg64s.get64, BitVec.sub_eq_add_neg] using hm
    simp only [Effects.All]
    natdiv_step 180 using hc
    natdiv_step 181 using hc
    natdiv_step 182 using hc
    by_cases secondWord : (s.regs.r10.toNat + 1) % 18446744073709551616 < s.regs.rdx.toNat
    · simpa [first, firstAddress, get, Reg64s.get64, StatusFlags.from_result,
        incrementNat, secondWord, target652, Effects.All, BitVec.sub_eq_add_neg,
        BitVec.ofInt_add, BitVec.ofInt_toInt] using next _
    · simp [StatusFlags.from_result, incrementNat, secondWord, Effects.All]
      natdiv_step 183 using hc
      simpa [first, firstAddress, get, Reg64s.get64, secondWord, BitVec.sub_eq_add_neg,
        BitVec.ofInt_add, BitVec.ofInt_toInt] using next _
  · have branch : s.regs.rdx.toNat ≤ s.regs.r10.toNat := by omega
    simp [StatusFlags.from_result, branch, target697]
    have zero := missing presentWord
    subst value
    natdiv_step 184 using hc
    constructor <;> natdiv_step 185 using hc
    all_goals
      simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
      apply Delimited.store_cps
      · simpa [firstAddress, get, Reg64s.get64, BitVec.sub_eq_add_neg] using hm
      simp only [Effects.All]
      natdiv_step 186 using hc
      natdiv_step 187 using hc
      natdiv_step 188 using hc
      by_cases secondWord : (s.regs.r10.toNat + 1) % 18446744073709551616 < s.regs.rdx.toNat
      · simpa [first, firstAddress, get, Reg64s.get64, StatusFlags.from_result,
          incrementNat, secondWord, target652, Effects.All, BitVec.sub_eq_add_neg,
          BitVec.ofInt_add, BitVec.ofInt_toInt] using next _
      · simpa [first, firstAddress, get, Reg64s.get64, StatusFlags.from_result,
          incrementNat, secondWord, Effects.All, BitVec.sub_eq_add_neg,
          BitVec.ofInt_add, BitVec.ofInt_toInt] using next _

def second (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r11 := UInt64.ofBitVec value
      r10 := UInt64.ofBitVec (get s .r10 + 1#64)}
    dmem := Mem.storeInt s.dmem (get s .r9 + get s .r8 * 8#64) 8 value.toInt
    status := flags}

/-- Loaded second limbs execute MOV/load, MOV/store, INC, CMP, JE. -/
theorem second_present_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (loaded : Mem.loadInt s.dmem (get s .rsi + get s .r8 * 8#64 + 8#64) 8 =
      some (value.toNat : Int))
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r9 + get s .r8 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (second s value flags, if get s .r10 + 1#64 = get s .rcx
        then base + 729 else base + 669)) :
    Eventually (step e) P (s, base + 652) := by
  have target729 := hc.targets ("natDivision_u729", 729) (by decide)
  simp only [get, Reg64s.get64] at loaded
  natdiv_step 170 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natdiv_load loaded
  natdiv_step 171 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simp only [Effects.All]
  natdiv_step 172 using hc
  natdiv_step 173 using hc
  natdiv_step 174 using hc
  by_cases done : s.regs.r10.toBitVec + 1#64 = s.regs.rcx.toBitVec
  · have doneReg : s.regs.r10 + 1 = s.regs.rcx := by
      apply UInt64.toBitVec_inj.mp
      exact done
    simpa [second, get, Reg64s.get64, StatusFlags.from_result,
      done, doneReg, target729, Effects.All] using next _
  · simpa [second, get, Reg64s.get64, StatusFlags.from_result,
      done, Effects.All] using next _

/-- An absent second limb is explicitly zeroed and stored, not merely skipped. -/
theorem second_missing_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r9 + get s .r8 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (second s 0 flags, if get s .r10 + 1#64 = get s .rcx
        then base + 729 else base + 669)) :
    Eventually (step e) P (s, base + 714) := by
  have target669 := hc.targets ("natDivision_u669", 669) (by decide)
  natdiv_step 189 using hc
  constructor <;> natdiv_step 190 using hc
  all_goals
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    apply Delimited.store_cps
    · exact hm
    simp only [Effects.All]
    natdiv_step 191 using hc
    natdiv_step 192 using hc
    natdiv_step 193 using hc
    by_cases done : s.regs.r10.toBitVec + 1#64 = s.regs.rcx.toBitVec
    · have doneReg : s.regs.r10 + 1 = s.regs.rcx := by
        apply UInt64.toBitVec_inj.mp
        exact done
      simpa [second, get, Reg64s.get64, StatusFlags.from_result,
        done, doneReg, Effects.All] using next _
    · simpa [second, get, Reg64s.get64, StatusFlags.from_result,
        done, target669, Effects.All] using next _

/-- An opaque complete two-word iteration, including all source bounds checks. -/
def pair (s : MachineData) (a b : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := s.regs.r10
      r10 := UInt64.ofBitVec (get s .r10 + 2#64)
      r11 := UInt64.ofBitVec b}
    dmem := Mem.storeInt (Mem.storeInt s.dmem (firstAddress s) 8 a.toInt)
      (get s .r9 + get s .r10 * 8#64) 8 b.toInt
    status := flags}

theorem pair_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a b : BitVec 64)
    (firstLoad : (get s .r10).toNat < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rsi + get s .r10 * 8#64) 8 = some (a.toNat : Int))
    (firstZero : ¬ (get s .r10).toNat < (get s .rdx).toNat → a = 0)
    (firstMapped : ∃ old, Mem.loadInt s.dmem (firstAddress s) 8 = some old)
    (secondLoad : (get s .r10 + 1#64).toNat < (get s .rdx).toNat →
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 a.toInt)
        (get s .rsi + get s .r10 * 8#64 + 8#64) 8 = some (b.toNat : Int))
    (secondZero : ¬ (get s .r10 + 1#64).toNat < (get s .rdx).toNat → b = 0)
    (secondMapped : ∃ old,
      Mem.loadInt (Mem.storeInt s.dmem (firstAddress s) 8 a.toInt)
        (get s .r9 + get s .r10 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (pair s a b flags, if get s .r10 + 2#64 = get s .rcx
        then base + 729 else base + 669)) :
    Eventually (step e) P (s, base + 669) := by
  apply first_cps e base hc s a firstLoad firstZero firstMapped P
  intro flags
  have image : ∀ flags', second (first s a flags) b flags' = pair s a b flags' := by
    intro flags'
    simp only [second, first, pair, get, Reg64s.get64, UInt64.toBitVec_ofBitVec,
      BitVec.add_assoc, show 1#64 + 1#64 = 2#64 by decide]
  have counter : get (first s a flags) .r10 + 1#64 = get s .r10 + 2#64 := by
    change (get s .r10 + 1#64) + 1#64 = get s .r10 + 2#64
    bv_omega
  have countReg : get (first s a flags) .rcx = get s .rcx := rfl
  by_cases present : (get s .r10 + 1#64).toNat < (get s .rdx).toNat
  · simp only [present, ↓reduceIte]
    apply second_present_cps e base hc _ b
    · exact secondLoad present
    · exact secondMapped
    intro flags'
    rw [image]
    rw [counter, countReg]
    exact next flags'
  · simp only [present, ↓reduceIte]
    have zero := secondZero present
    subst b
    apply second_missing_cps e base hc
    · exact secondMapped
    intro flags'
    rw [image]
    rw [counter, countReg]
    exact next flags'

end SszX86.NatDivision.Copy
