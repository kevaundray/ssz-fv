import SszX86.NatAddStack
import SszX86.NatAddProtected

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem stack_store_frame (m : DataMem) (sp a : BitVec 64)
    (distance : Nat) (value : Int) (low : 8 ≤ distance) (high : distance ≤ 48)
    (outside : ∀ i < 48, a ≠ (sp - 48) + BitVec.ofNat 64 i) :
    (Mem.storeInt m (sp - BitVec.ofNat 64 distance) 8 value).get? a = m.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  have index : i < 8 := by simpa only [Int.toBytes_length] using hi
  have eq : sp - BitVec.ofNat 64 distance + BitVec.ofNat 64 i =
      (sp - 48) + BitVec.ofNat 64 (48-distance+i) := by bv_omega
  rw [eq]
  exact outside (48-distance+i) (by omega)

/-- The tighter activation frame does not grant the pilot's unrelated locals. -/
theorem pushed_frame (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 48, a ≠ (s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 i) :
    (pushedMem s).get? a = s.dmem.get? a := by
  simp (disch := first | assumption | decide | omega) only
    [pushedMem, Delimited.pushedMem, BitVec.ofNat_eq_ofNat, stack_store_frame]

theorem pushed_model_frame (s : MachineData) (outcome : NatArithmetic.Outcome NatOperand)
    (low : 48 ≤ s.regs.rsp.toNat) : Frame s (pushedMem s) outcome := by
  intro a _ outside _
  change 48 ≤ s.regs.rsp.toBitVec.toNat at low
  change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat - 48) 48 at outside
  apply pushed_frame
  intro i hi
  unfold Body.Outside at outside
  bv_omega

theorem pushed_operands (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra) :
    left.At (widthLoad (pushedMem s)) ∧ right.At (widthLoad (pushedMem s)) := by
  have frame := pushed_model_frame s
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) owned.stack_low
  exact ⟨operand_preserved s left right left address capacity used ra owned _ frame
      owned.left_at owned.left_owned,
    operand_preserved s left right right address capacity used ra owned _ frame
      owned.right_at owned.right_owned⟩

theorem pushed_load (s : MachineData) (p : BitVec 64) (n : Nat)
    (bound : p.toNat + n ≤ 2^64) (low : 48 ≤ s.regs.rsp.toNat)
    (apart : Body.Apart p.toNat n (s.regs.rsp.toNat - 48) 48) :
    Mem.loadInt (pushedMem s) p n = Mem.loadInt s.dmem p n := by
  change 48 ≤ s.regs.rsp.toBitVec.toNat at low
  change Body.Apart p.toNat n (s.regs.rsp.toBitVec.toNat - 48) 48 at apart
  apply memmove_loadInt_congr
  intro i hi
  apply pushed_frame
  intro j hj
  unfold Body.Apart at apart
  bv_omega

theorem pushed_header (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra) :
    Mem.loadInt (pushedMem s) s.regs.r9.toBitVec 8 = some (address.toNat : Int) ∧
      Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec + 8) 8 = some (capacity.toNat : Int) ∧
      Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec + 16) 8 = some (used.toNat : Int) := by
  have unchanged (off : Nat) (inside : off + 8 ≤ 24) :
      Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt s.dmem (s.regs.r9.toBitVec + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply pushed_frame
    intro j hj
    have low := owned.stack_low
    have bound := owned.header_bound
    have apart := owned.header_stack
    change 48 ≤ s.regs.rsp.toBitVec.toNat at low
    change s.regs.r9.toBitVec.toNat + 24 ≤ 2^64 at bound
    change Body.Apart s.regs.r9.toBitVec.toNat 24 (s.regs.rsp.toBitVec.toNat - 48) 48 at apart
    unfold Body.Apart at apart
    bv_omega
  refine ⟨?_, ?_, ?_⟩
  · have eq := unchanged 0 (by decide)
    simp only [BitVec.add_zero] at eq
    exact eq.trans owned.address_load
  · exact (unchanged 8 (by decide)).trans owned.capacity_load
  · exact (unchanged 16 (by decide)).trans owned.used_load

end SszX86.NatAdd
