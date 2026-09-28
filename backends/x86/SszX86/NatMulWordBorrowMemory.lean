import SszX86.NatMulWordOwnership
import SszX86.NatMulWordBorrow
import SszX86.NatMulWordOutput

namespace SszX86.NatMulWord
open SszNative UintCodec
open NatToU128 (ByteFrame narrow_load_preserved narrow_width_preserved)

theorem success_output_frame (m : DataMem) (out pointer payload : BitVec 64)
    (bound : out.toNat + 72 ≤ 2^64) :
    ByteFrame m (successMem m out pointer payload) out.toNat 72 := by
  intro a outside
  apply NatAdd.success_mem_frame
  intro i hi
  exact Body.outside_byte out a 72 i bound outside (by omega)

theorem zero_output_frame (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 72 ≤ 2^64) : ByteFrame m (zeroMem m out) out.toNat 72 := by
  intro a outside
  apply zero_mem_frame
  · intro i hi
    exact Body.outside_byte out a 72 i bound outside (by omega)
  · intro i hi
    have same := Body.outside_byte out a 72 (64+i) bound outside (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using same

/-- Physical input observations are derived from entry ownership and the exact
publication frame, rather than assumed in a future state. -/
theorem operand_after_output (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (frame : ByteFrame s.dmem m s.regs.rdi.toNat 72) :
    operand.At (widthLoad m) := by
  cases operand with
  | small limb => trivial
  | large p words =>
    obtain ⟨positive, aligned, bound, observed⟩ := owned.operand_at
    have protection := owned.operand_owned
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    have inside := i.isLt
    rw [narrow_width_preserved s.dmem m s.regs.rdi.toNat 72 (p.toNat+8*i.val) 8 frame
      (by omega) (by
        have separated := protection.output
        simp only [Body.Apart] at separated ⊢
        omega)]
    exact observed i

theorem return_after_output (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (frame : ByteFrame s.dmem m s.regs.rdi.toNat 72) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have same := narrow_load_preserved s.dmem m s.regs.rdi.toNat 72 s.regs.rsp.toNat 8
    frame owned.return_bound owned.output_return.symm
  simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, owned.return_load] using same

theorem cursor_after_output (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (frame : ByteFrame s.dmem m s.regs.rdi.toNat 72) :
    widthLoad m (s.regs.r8.toNat + 16) 8 = some used.toNat := by
  rw [narrow_width_preserved s.dmem m s.regs.rdi.toNat 72 (s.regs.r8.toNat+16) 8 frame
    (by have := owned.header_bound; omega) (by
      have separated := owned.header_output
      simp only [Body.Apart] at separated ⊢
      omega)]
  unfold widthLoad
  rw [show BitVec.ofNat 64 (s.regs.r8.toNat + 16) = s.regs.r8.toBitVec + 16 by
    change BitVec.ofNat 64 (s.regs.r8.toBitVec.toNat + 16) = _
    exact width_address s.regs.r8.toBitVec 16,
    owned.used_load]
  rfl

theorem success_exact_frame (s : MachineData) (result : NatOperand) (used : Nat)
    (bound : s.regs.rdi.toNat + 72 ≤ 2^64) :
    Frame s (successMem s.dmem s.regs.rdi.toBitVec result.pointer result.payload)
      (NatArithmetic.unchanged used (.ok result)) := by
  intro a output activation allocation
  apply NatFromU128.success_frame
  · intro i hi
    exact Body.outside_byte s.regs.rdi.toBitVec a 16 i (by
      simp only [UInt64.toNat_toBitVec]
      omega) output.1 hi
  · intro i hi
    have outside := output.2
    simp only [← UInt64.toNat_toBitVec, Body.Outside] at bound outside
    bv_omega

theorem zero_exact_frame (s : MachineData) (used : Nat)
    (bound : s.regs.rdi.toNat + 72 ≤ 2^64) :
    Frame s (zeroMem s.dmem s.regs.rdi.toBitVec)
      (NatArithmetic.unchanged used (.ok (.small 0))) := by
  intro a output activation allocation
  apply zero_mem_frame
  · intro i hi
    exact Body.outside_byte s.regs.rdi.toBitVec a 16 i (by
      simp only [UInt64.toNat_toBitVec]
      omega) output.1 hi
  · intro i hi
    have outside := output.2
    simp only [← UInt64.toNat_toBitVec, Body.Outside] at bound outside
    bv_omega

end SszX86.NatMulWord
