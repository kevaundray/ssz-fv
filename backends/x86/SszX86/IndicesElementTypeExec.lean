import SszX86.IndicesElementTypeImpl
import SszX86.CodecNatCmpUsizeExec
import SszX86.CodecStorage
import SszIndicesDescriptor

namespace SszX86.IndicesElementType
open Kraken.X64.Parser
open SszNative UintCodec

macro "indices_element_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.IndicesElementType.step_at _ _ $hc
     (SszX86.IndicesElementType.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.IndicesElementType.program,
     SszX86.IndicesElementType.programChunk0, SszX86.IndicesElementType.programChunk1,
     List.cons_append, List.nil_append, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesElementType.directives, SszX86.IndicesElementType.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "indices_element_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), NatCompare.word_cast])

/-- The first branch observes the actual PathStep tag before dispatching Desc. -/
theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pathTag descTag : BitVec 64)
    (hp : Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 = some (pathTag.toNat : Int))
    (hd : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (descTag.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := UInt64.ofBitVec descTag}, status := flags},
        if pathTag = 0 then base + 35 else base + 9)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("indices_element_type_u35", 35) (by decide)
  rw [← Int64.add_zero base]
  indices_element_step 0 using hc
  indices_element_load hp
  indices_element_step 1 using hc
  indices_element_load hd
  indices_element_step 2 using hc
  by_cases hz : pathTag = 0#64
  · simpa [hz, StatusFlags.from_result, Effects.All, target] using next _
  · simpa [hz, StatusFlags.from_result, Effects.All] using next _

/-- Only RDX, R9 and flags are modified by the backwards high-zero scan.
RCX retains the original physical length for NoSuchField's borrowed payload. -/
def scanState (s : MachineData) (count previous : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rdx := UInt64.ofBitVec count,
    r9 := UInt64.ofBitVec previous}, status := flags}

/-- One actual iteration of PCs 240 through 259, including the memory CMP. -/
theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (previous limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2^64)
    (hl : Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 240))
    (nonzero : limb ≠ 0 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 261)) :
    Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+2)) previous flags, base + 240) := by
  have target := hc.targets ("indices_element_type_u240", 240) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) =
      BitVec.ofNat 64 (n+1) := by bv_omega
  have addr : BitVec.ofInt 64 (s.regs.r8.toBitVec.toInt +
      (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      s.regs.r8.toBitVec + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    bv_omega
  indices_element_step 51 using hc
  indices_element_step 52 using hc
  simp [scanState, StatusFlags.from_result, ne, Effects.All]
  indices_element_step 53 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  indices_element_step 54 using hc
  rw [addr]
  indices_element_load hl
  indices_element_step 55 using hc
  indices_element_step 56 using hc
  by_cases hz : limb = 0#64
  · simpa [scanState, StatusFlags.from_result, hz, target, Effects.All] using zero hz _
  · simpa [scanState, StatusFlags.from_result, hz, Effects.All] using nonzero hz _

/-- The scan terminates for every physical limb list, including emptyLarge and
arbitrarily many noncanonical high zeros. No canonicality premise is used. -/
theorem scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length + 1 < 2^64)
    (loads : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ previous flags,
      (Limbs.significantCount words n = 0 → ∀ previous flags, Eventually (step e) P
        (scanState s 1 previous flags, base + 269)) →
      (0 < Limbs.significantCount words n → ∀ flags, Eventually (step e) P
        (scanState s (BitVec.ofNat 64 (Limbs.significantCount words n))
          (BitVec.ofNat 64 (Limbs.significantCount words n)) flags, base + 261)) →
      Eventually (step e) P
        (scanState s (BitVec.ofNat 64 (n+1)) previous flags, base + 240) := by
  intro n
  induction n with
  | zero =>
    intro hn previous flags zero nonzero
    have target := hc.targets ("indices_element_type_u269", 269) (by decide)
    indices_element_step 51 using hc
    indices_element_step 52 using hc
    simpa [scanState, StatusFlags.from_result, target, Effects.All] using zero rfl previous _
  | succ n ih =>
    intro hn previous flags zero nonzero
    have hl : Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using loads ⟨n, by omega⟩
    apply scan_step e base hc s previous _ flags n (by omega) hl P
    · intro hz fl
      apply ih (by omega) _ fl
      · simpa [Limbs.significantCount, hz] using zero
      · simpa [Limbs.significantCount, hz] using nonzero
    · intro hz fl
      simpa [Limbs.significantCount, hz] using
        nonzero (by simp [Limbs.significantCount, hz]) fl

end SszX86.IndicesElementType
