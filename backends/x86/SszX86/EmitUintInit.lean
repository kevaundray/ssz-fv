import SszX86.EmitUintTail

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get put putF compare subFlags shift)

def pairReady (s : MachineData) (large : Bool) (flags : StatusFlags) : MachineData :=
  let even := get s .rsi &&& 0xfffffffffffffffe#64
  {s with
    regs := {s.regs with
      rax := 0
      r9 := 0
      rdi := if large then s.regs.rdi else UInt64.ofBitVec even
      r8 := if large then UInt64.ofBitVec even else s.regs.r8}
    status := flags}

theorem pair_setup (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (large : Bool) (P : MachineState → Prop)
    (many : get s .rsi ≠ 1#64)
    (next : ∀ flags, Eventually (step e) P
      (pairReady s large flags, base + if large then 946 else 1056)) :
    Eventually (step e) P (s, base + if large then 616 else 876) := by
  have different : s.regs.rsi.toBitVec ≠ 1#64 := by
    simpa only [UintCodec.Large.get, Reg64s.get64] using many
  have branch := beq_eq_false_iff_ne.mpr different
  cases large
  · uint_exec at876 using hc
    uint_exec at880 using hc
    simp only [BitVec.ofNat_eq_ofNat, branch, Bool.false_eq_true, ↓reduceIte]
    uint_exec at1035 using hc
    uint_exec at1038 using hc
    uint_exec at1042 using hc
    uint_exec at1045 using hc
    uint_exec at1047 using hc
    simpa [pairReady, UintCodec.Large.get, Reg64s.get64] using next _
  · uint_exec at616 using hc
    uint_exec at620 using hc
    simp only [BitVec.ofNat_eq_ofNat, branch, Bool.false_eq_true, ↓reduceIte]
    uint_exec at893 using hc
    uint_exec at896 using hc
    uint_exec at900 using hc
    uint_exec at903 using hc
    uint_exec at905 using hc
    simpa [pairReady, UintCodec.Large.get, Reg64s.get64] using next _

/-- Width-one Small takes the actual scalar shortcut, not the pair loop. -/
theorem one_small_setup (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (one : get s .rsi = 1#64)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0}, status := flags}, base + 1136)) :
    Eventually (step e) P (s, base + 876) := by
  have rawOne : s.regs.rsi.toBitVec = 1#64 := by
    simpa only [UintCodec.Large.get, Reg64s.get64] using one
  uint_exec at876 using hc
  uint_exec at880 using hc
  simp only [BitVec.ofNat_eq_ofNat, rawOne, beq_self_eq_true, ↓reduceIte]
  uint_exec at886 using hc
  uint_exec at888 using hc
  exact next _

/-- Width-one Large performs the actual physical-count guarded first-limb read,
including the legitimate non-null Large [] zero-extension case. -/
theorem one_large_setup (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (P : MachineState → Prop)
    (one : get s .rsi = 1#64)
    (read : 0 < (get s .rdx).toNat → Mem.loadInt s.dmem (get s .rdi) 8 = some (limb.toNat : Int))
    (zero : (get s .rdx).toNat = 0 → limb = 0)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rax := 0, rcx := 0, rdx := UInt64.ofBitVec limb}
        status := flags}, base + 1136)) :
    Eventually (step e) P (s, base + 616) := by
  have rawOne : s.regs.rsi.toBitVec = 1#64 := by
    simpa only [UintCodec.Large.get, Reg64s.get64] using one
  uint_exec at616 using hc
  uint_exec at620 using hc
  simp only [BitVec.ofNat_eq_ofNat, rawOne, beq_self_eq_true, ↓reduceIte]
  uint_exec at626 using hc
  uint_exec at628 using hc
  uint_exec at631 using hc
  uint_exec at635 using hc
  uint_exec at638 using hc
  simp only [BitVec.ofNat_eq_ofNat,
    show (0#64 >>> (3 : Nat)) = 0#64 by decide,
    show (0#64).toNat = 0 by decide, UInt64.toNat_toBitVec]
  by_cases positive : 0 < (get s .rdx).toNat
  · have comparison : 0 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using positive
    simp only [comparison, decide_true, ↓reduceIte]
    refine at644 e base hc _ limb ?_ (by simp [Writable]) P ?_
    · simpa [Read, readAddress, UintCodec.Large.get, Reg64s.get64, BitVec.ofNat_eq_ofNat] using read positive
    intro flags
    simp only [instruction, Instructions.next, UintCodec.Large.put, Reg64s.set64]
    uint_exec at648 using hc
    with_unfolding_all exact next _
  · have comparison : ¬ 0 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using positive
    simp only [comparison, decide_false, Bool.false_eq_true, ↓reduceIte]
    have empty := zero (by omega)
    subst limb
    uint_exec at1031 using hc
    uint_exec at1033 using hc
    with_unfolding_all exact next _

/-- The low-bit test decides the actual even/odd terminal path. -/
theorem pair_parity (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (large : Bool) (count : Nat) (P : MachineState → Prop)
    (length : get s .rsi = BitVec.ofNat 64 count)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags},
        if count % 2 = 0 then base + 1147 else base + if large then 1012 else 1119)) :
    Eventually (step e) P (s, base + if large then 1002 else 1113) := by
  have rawLength : s.regs.rsi.toBitVec = BitVec.ofNat 64 count := length
  have maskZero : (s.regs.rsi.toBitVec.setWidth 8 &&& 1#8) = 0#8 ↔ count % 2 = 0 := by
    rw [rawLength]
    exact count_parity count
  have flagTrue (even : count % 2 = 0) :
      ((s.regs.rsi.toBitVec.setWidth 8 &&& 1#8) == BitVec.zero 8) = true :=
    beq_iff_eq.mpr (maskZero.mpr even)
  have flagFalse (odd : count % 2 ≠ 0) :
      ((s.regs.rsi.toBitVec.setWidth 8 &&& 1#8) == BitVec.zero 8) = false :=
    beq_eq_false_iff_ne.mpr (fun equal => odd (maskZero.mp equal))
  cases large
  · uint_exec at1113 using hc
    uint_exec at1117 using hc
    by_cases even : count % 2 = 0
    · simp only [StatusFlags.from_result, BitVec.ofNat_eq_ofNat, flagTrue even, ↓reduceIte]
      simp only [even, ↓reduceIte] at next
      exact next _
    · simp only [StatusFlags.from_result, BitVec.ofNat_eq_ofNat, flagFalse even,
        Bool.false_eq_true, ↓reduceIte]
      simp only [even, ↓reduceIte] at next
      exact next _
  · uint_exec at1002 using hc
    uint_exec at1006 using hc
    by_cases even : count % 2 = 0
    · simp only [StatusFlags.from_result, BitVec.ofNat_eq_ofNat, flagTrue even, ↓reduceIte]
      simp only [even, ↓reduceIte] at next
      exact next _
    · simp only [StatusFlags.from_result, BitVec.ofNat_eq_ofNat, flagFalse even,
        Bool.false_eq_true, ↓reduceIte]
      simp only [even, ↓reduceIte] at next
      exact next _

theorem large_tail_advance (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with r14 := UInt64.ofBitVec (get s .r14 + get s .rax)}
        status := flags}, base + 1015)) :
    Eventually (step e) P (s, base + 1012) := by
  uint_exec at1012 using hc
  exact next _

end SszX86.Emit.Uint
