import SszX86.EmitUintLoop

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open SszNative
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get put putF compare subFlags shift)

def scalarTail (s : MachineData) (flags : StatusFlags) : MachineData :=
  let count := low32 (((get s .rax).setWidth 32 <<< (3 : Nat)).setWidth 64)
  let shifted := get s .rdx >>> ((low8 count).toNat &&& 63)
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec count
      rcx := UInt64.ofBitVec count
      rdx := UInt64.ofBitVec shifted}
    status := flags
    dmem := Mem.storeInt s.dmem (get s .r14) 1 (low8 shifted).toInt}

/-- The actual common SHLL/MOVL/SHRQ/MOVB scalar suffix. -/
theorem scalar_tail_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem s.regs.r14.toBitVec 1 = some old)
    (next : ∀ flags, Eventually (step e) P (scalarTail s flags, base + 1147)) :
    Eventually (step e) P (s, base + 1136) := by
  uint_exec at1136 using hc
  uint_exec at1139 using hc
  uint_exec at1141 using hc
  uint_write at1144 using hc mapped hmap
  simpa [scalarTail, low8, low32, UintCodec.Large.get, UintCodec.Large.shift, Reg64s.get64] using next _

/-- The scalar suffix writes exactly the selected limb byte at the original
output position; all high byte indices are handled by the hardware shift mask. -/
theorem scalar_tail_memory (s : MachineData) (limbs : List (BitVec 64)) (index : Nat)
    (flags : StatusFlags) (indexEq : get s .rax = BitVec.ofNat 64 index)
    (selected : get s .rdx = limbs[index / 8]?.getD 0) :
    (scalarTail s flags).dmem =
      Mem.storeInt s.dmem (get s .r14) 1 (Limbs.byteAt limbs index).toBitVec.toInt := by
  have extracted := congrArg UInt8.toBitVec (shifted_limb_byte limbs index)
  simp only [scalarTail, indexEq, selected, tail_shift]
  exact congrArg (fun byte : BitVec 8 => Mem.storeInt s.dmem (get s .r14) 1 byte.toInt) extracted

/-- Live low-bit TEST agrees with parity for arbitrary physical count. -/
theorem count_parity (count : Nat) :
    ((BitVec.ofNat 64 count).setWidth 8 &&& 1#8) = 0#8 ↔ count % 2 = 0 := by
  have mod : (((BitVec.ofNat 64 count).setWidth 8 &&& 1#8)).toNat = count % 2 := by
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change ((count % 2 ^ 64) % 2 ^ 8) &&& 1 = count % 2
    rw [Nat.and_one_is_mod]
    omega
  constructor
  · intro zero
    rw [zero] at mod
    simpa using mod.symm
  · intro even
    apply BitVec.eq_of_toNat_eq
    simp only [mod, even, BitVec.toNat_ofNat, Nat.zero_mod]

/-- Small's odd-tail setup advances by the last completed pair and conditionally
zeroes the original Small word beyond byte seven. -/
theorem small_tail_setup (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with
          r14 := UInt64.ofBitVec (get s .r14 + get s .r8 + 2)
          rcx := 0
          rdx := UInt64.ofBitVec (if (get s .rax).toNat < 8 then get s .rdx else 0)}
        status := flags}, base + 1136)) :
    Eventually (step e) P (s, base + 1119) := by
  uint_exec at1119 using hc
  uint_exec at1122 using hc
  uint_exec at1126 using hc
  uint_exec at1128 using hc
  uint_exec at1132 using hc
  have selected := next (UintCodec.Large.subFlags s.regs.rax.toBitVec 8#64)
  simp [UintCodec.Large.get, Reg64s.get64, BitVec.ofNat_eq_ofNat] at selected ⊢
  with_unfolding_all exact selected

/-- Large's scalar read uses the same physical bounds check as the pair loop. -/
theorem large_tail_select (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (P : MachineState → Prop)
    (read : (get s .rax).toNat / 8 < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rdi + BitVec.ofNat 64 (8 * ((get s .rax).toNat / 8))) 8 =
        some (limb.toNat : Int))
    (zero : (get s .rdx).toNat ≤ (get s .rax).toNat / 8 → limb = 0)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with
          rcx := UInt64.ofBitVec (get s .rax >>> (3 : Nat))
          rdx := UInt64.ofBitVec limb}
        status := flags}, base + 1136)) :
    Eventually (step e) P (s, base + 1015) := by
  have indexNat : (get s .rax >>> (3 : Nat)).toNat = (get s .rax).toNat / 8 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have indexBits : get s .rax >>> (3 : Nat) = BitVec.ofNat 64 ((get s .rax).toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [indexNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (get s .rax).isLt; omega)]
  have guardIndex : (s.regs.rax.toBitVec >>> (3 : Nat)).toNat = s.regs.rax.toNat / 8 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_toBitVec]
  have address : get s .rdi + (get s .rax >>> (3 : Nat)) * 8 =
      get s .rdi + BitVec.ofNat 64 (8 * ((get s .rax).toNat / 8)) := by
    simp only [BitVec.ofNat_eq_ofNat]
    rw [indexBits, ← BitVec.ofNat_mul, Nat.mul_comm]
  uint_exec at1015 using hc
  uint_exec at1018 using hc
  uint_exec at1022 using hc
  uint_exec at1025 using hc
  by_cases inside : (get s .rax).toNat / 8 < (get s .rdx).toNat
  · have comparison : s.regs.rax.toNat / 8 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using inside
    simp only [guardIndex, UInt64.toNat_toBitVec, comparison, decide_true, ↓reduceIte]
    have loaded : Mem.loadInt s.dmem (get s .rdi + (get s .rax >>> (3 : Nat)) * 8) 8 =
        some (limb.toNat : Int) := by
      rw [address]
      exact read inside
    refine at644 e base hc _ limb ?_ (by simp [Writable]) P ?_
    · simpa [Read, readAddress, UintCodec.Large.get, Reg64s.get64] using loaded
    intro loadFlags
    simp only [instruction, Instructions.next, UintCodec.Large.put, Reg64s.set64]
    uint_exec at648 using hc
    with_unfolding_all exact next _
  · have comparison : ¬ s.regs.rax.toNat / 8 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using inside
    simp only [guardIndex, UInt64.toNat_toBitVec, comparison, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    have empty := zero (by omega)
    subst limb
    uint_exec at1031 using hc
    uint_exec at1033 using hc
    with_unfolding_all exact next _

end SszX86.Emit.Uint
