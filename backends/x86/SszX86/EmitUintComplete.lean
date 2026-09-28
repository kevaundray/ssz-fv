import SszX86.EmitUintFinish

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open SszNative
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get)

theorem LoopInv.flags {original current : MachineData} {number : NatOperand} {count index : Nat}
    (inv : LoopInv original current number count index) (flags : StatusFlags) :
    LoopInv original {current with status := flags} number count index := by
  cases number <;>
    exact ⟨inv.stack, inv.result, inv.output, inv.vector, inv.length, inv.indexReg, inv.counter,
      inv.payload, inv.source, inv.limit, inv.lastSmallIndex, inv.hprefix⟩

/-- One remaining byte, followed by the real length store. This internal lemma
has only the current register invariant and the original static Owned record. -/
theorem complete_scalar (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original current : MachineData) (logicalWidth number : NatOperand) (count index : Nat)
    (owned : Owned original logicalWidth number count)
    (last : index + 1 = count)
    (stack : current.regs.rsp = original.regs.rsp)
    (result : current.regs.rbx = original.regs.rbx)
    (vector : current.zmms = original.zmms)
    (length : get current .rsi = BitVec.ofNat 64 count)
    (output : get current .r14 = original.regs.r14.toBitVec + BitVec.ofNat 64 index)
    (indexEq : get current .rax = BitVec.ofNat 64 index)
    (selected : get current .rdx = number.words[index / 8]?.getD 0)
    (hprefix : Prefix original.dmem current.dmem original.regs.r14.toBitVec
      (Limbs.bytes number.words count) index) :
    Eventually (step e) (OutputPost original number count base) (current, base + 1136) := by
  have static := LoopOwned.of_owned original logicalWidth number count owned
  have hmap : Large.Mapped current.dmem original.regs.r14.toBitVec count := by
    simpa only [Limbs.bytes, Array.size_ofFn] using prefix_mapped hprefix
      (by simpa only [Large.Mapped, Limbs.bytes, Array.size_ofFn] using owned.output)
      (by simpa only [Limbs.bytes, Array.size_ofFn] using Nat.le_of_lt static.bounded)
  apply scalar_tail_runs e base hc current
  · change ∃ old, Mem.loadInt current.dmem (get current .r14) 1 = some old
    rw [output]
    exact Large.mapped_load _ _ count index 1 hmap (by omega)
  · intro flags
    apply finish_runs e base hc original (scalarTail current flags) logicalWidth number count owned
    · exact stack
    · exact result
    · exact vector
    · exact length
    · have extended := prefix_store hprefix
        (by simpa only [Limbs.bytes, Array.size_ofFn, UInt64.toNat_toBitVec] using owned.output_bound)
        (by simpa only [Limbs.bytes, Array.size_ofFn] using (by omega : index < count))
      rw [scalar_tail_memory current number.words index flags indexEq selected, output]
      simpa only [Limbs.bytes, Array.getElem_ofFn, last] using extended

/-- Both even and odd Small loop exits are discharged. The actual R8+2
pointer advance is related to the last completed pair by LoopInv. -/
theorem small_complete (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original current : MachineData) (logicalWidth : NatOperand) (limb : BitVec 64) (count : Nat)
    (owned : Owned original logicalWidth (.small limb) count) (many : 2 ≤ count)
    (inv : LoopInv original current (.small limb) count (2 * (count / 2))) :
    Eventually (step e) (OutputPost original (.small limb) count base) (current, base + 1113) := by
  apply pair_parity e base hc current false count _ inv.length
  intro flags
  let tested := {current with status := flags}
  have testedInv := inv.flags flags
  by_cases even : count % 2 = 0
  · simp only [even, ↓reduceIte]
    apply finish_runs e base hc original tested logicalWidth (.small limb) count owned
      testedInv.stack testedInv.result testedInv.vector testedInv.length
    have equal : 2 * (count / 2) = count := by omega
    simpa only [equal] using testedInv.hprefix
  · simp only [even, ↓reduceIte]
    apply small_tail_setup e base hc tested
    intro flags'
    apply complete_scalar e base hc original _ logicalWidth (.small limb) count (2 * (count / 2)) owned
    · omega
    · exact testedInv.stack
    · exact testedInv.result
    · exact testedInv.vector
    · exact testedInv.length
    · change get tested .r14 + get tested .r8 + 2#64 = _
      have out : get tested .r14 = original.regs.r14.toBitVec := by
        simpa only [UintCodec.Large.get, Reg64s.get64] using
          congrArg UInt64.toBitVec testedInv.output
      rw [out, testedInv.lastSmallIndex (by omega)]
      have advance : 2 * (count / 2) - 2 + 2 = 2 * (count / 2) := by omega
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, advance]
    · exact testedInv.indexReg
    · change (if (get tested .rax).toNat < 8 then get tested .rdx else 0) = _
      have physical : 2 * (count / 2) < 2 ^ 64 := by
        have bound := (LoopOwned.of_owned original logicalWidth (.small limb) count owned).bounded
        omega
      rw [testedInv.indexReg, testedInv.payload, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
      exact (small_limb limb (2 * (count / 2))).symm
    · exact testedInv.hprefix

/-- Large's odd suffix performs its own original-allocation bounds check and
load; no helper result or selected guard is supplied by the caller. -/
theorem large_complete (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original current : MachineData) (logicalWidth : NatOperand) (pointer : BitVec 64)
    (limbs : List (BitVec 64)) (count : Nat)
    (owned : Owned original logicalWidth (.large pointer limbs) count)
    (inv : LoopInv original current (.large pointer limbs) count (2 * (count / 2))) :
    Eventually (step e) (OutputPost original (.large pointer limbs) count base) (current, base + 1002) := by
  have static := LoopOwned.of_owned original logicalWidth (.large pointer limbs) count owned
  have countPhysical : limbs.length < 2 ^ 64 := by have := static.operand.2.2.1; omega
  have indexPhysical : 2 * (count / 2) < 2 ^ 64 := by have := static.bounded; omega
  apply pair_parity e base hc current true count _ inv.length
  intro flags
  let tested := {current with status := flags}
  have testedInv := inv.flags flags
  by_cases even : count % 2 = 0
  · simp only [even, ↓reduceIte]
    apply finish_runs e base hc original tested logicalWidth (.large pointer limbs) count owned
      testedInv.stack testedInv.result testedInv.vector testedInv.length
    have equal : 2 * (count / 2) = count := by omega
    simpa only [equal] using testedInv.hprefix
  · simp only [even, ↓reduceIte]
    apply large_tail_advance e base hc tested
    intro advanceFlags
    let advanced := {tested with
      regs := {tested.regs with r14 := UInt64.ofBitVec (get tested .r14 + get tested .rax)}
      status := advanceFlags}
    have offsetNat : (get advanced .rax).toNat = 2 * (count / 2) := by
      change (get tested .rax).toNat = _
      rw [testedInv.indexReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexPhysical]
    have lengthNat : (get advanced .rdx).toNat = limbs.length := by
      change (get tested .rdx).toNat = _
      rw [testedInv.payload]
      exact Nat.mod_eq_of_lt countPhysical
    apply large_tail_select e base hc advanced (limbs[(2 * (count / 2)) / 8]?.getD 0)
    · intro inside
      rw [offsetNat, lengthNat] at inside
      change Mem.loadInt tested.dmem (get tested .rdi + BitVec.ofNat 64
        (8 * ((get tested .rax).toNat / 8))) 8 = _
      rw [testedInv.source]
      have equal : (get tested .rax).toNat = 2 * (count / 2) := offsetNat
      rw [equal]
      exact loop_limb original tested pointer limbs count (2 * (count / 2))
        ((2 * (count / 2)) / 8) static testedInv inside
    · intro outside
      rw [offsetNat, lengthNat] at outside
      simp [List.getElem?_eq_none outside]
    · intro selectedFlags
      apply complete_scalar e base hc original _ logicalWidth (.large pointer limbs)
        count (2 * (count / 2)) owned
      · omega
      · exact testedInv.stack
      · exact testedInv.result
      · exact testedInv.vector
      · exact testedInv.length
      · change get tested .r14 + get tested .rax = _
        have out : get tested .r14 = original.regs.r14.toBitVec := by
          simpa only [UintCodec.Large.get, Reg64s.get64] using
            congrArg UInt64.toBitVec testedInv.output
        rw [out, testedInv.indexReg]
      · exact testedInv.indexReg
      · rfl
      · exact testedInv.hprefix

end SszX86.Emit.Uint
