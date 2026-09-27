import SszX86.DelimitedPrepared
import SszX86.DelimitedCompareOps
import SszX86.DelimitedCompare

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Reuse unsigned observation inversion for an arbitrary signed register store. -/
theorem stored_word_load (m : DataMem) (address value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m address 8 value.toInt) address 8 = some (value.toNat : Int) := by
  have observed : widthLoad (Mem.storeInt m address 8 value.toInt) address.toNat 8 =
      some value.toNat := by
    simpa only [widthLoad, BoolCodec.observe, BitVec.add_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using BoolCodec.observe_store64 m address 0 value
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    widthLoad_eq _ address.toNat 8 value.toNat observed

theorem savedAt_congr (m n : DataMem) (sp : BitVec 64) (original : MachineData)
    (same : ∀ i < 48, n.get? (sp + 40#64 + BitVec.ofNat 64 i) =
      m.get? (sp + 40#64 + BitVec.ofNat 64 i)) (saved : SavedAt m sp original) :
    SavedAt n sp original := by
  have contents (distance : Nat) (lo : 40 ≤ distance) (hi : distance + 8 ≤ 88) :
      Mem.loadInt n (sp + BitVec.ofNat 64 distance) 8 =
        Mem.loadInt m (sp + BitVec.ofNat 64 distance) 8 := by
    apply memmove_loadInt_congr
    intro i inside
    have address : sp + BitVec.ofNat 64 distance + BitVec.ofNat 64 i =
        sp + 40#64 + BitVec.ofNat 64 (distance-40+i) := by bv_omega
    rw [address]
    exact same (distance-40+i) (by omega)
  exact ⟨(contents 40 (by decide) (by decide)).trans saved.rbx,
    (contents 48 (by decide) (by decide)).trans saved.r12,
    (contents 56 (by decide) (by decide)).trans saved.r13,
    (contents 64 (by decide) (by decide)).trans saved.r14,
    (contents 72 (by decide) (by decide)).trans saved.r15,
    (contents 80 (by decide) (by decide)).trans saved.rbp⟩

/-- The five local spills and the CALL word are strictly below all six saved
register slots. This modular fact does not introduce a signed-address bound. -/
theorem savedAt_work (m n : DataMem) (sp : BitVec 64) (original : MachineData)
    (frame : ∀ a : BitVec 64,
      (∀ i < 56, a ≠ (sp - 16#64) + BitVec.ofNat 64 i) → n.get? a = m.get? a)
    (saved : SavedAt m sp original) : SavedAt n sp original := by
  apply savedAt_congr m n sp original _ saved
  intro i hi
  apply frame
  intro j hj
  bv_omega

private theorem work_store_frame (m : DataMem) (sp a distance : BitVec 64) (value : Int)
    (within : distance.toNat ≤ 32)
    (outside : ∀ i < 56, a ≠ (sp - 16#64) + BitVec.ofNat 64 i) :
    (Mem.storeInt m (sp + distance) 8 value).get? a = m.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  have inside : i < 8 := by simpa only [Int.toBytes_length] using hi
  have address : sp + distance + BitVec.ofNat 64 i =
      (sp - 16#64) + BitVec.ofNat 64 (16 + distance.toNat + i) := by bv_omega
  rw [address]
  exact outside (16 + distance.toNat + i) (by omega)

private theorem work_zero_frame (m : DataMem) (sp a : BitVec 64) (value : Int)
    (outside : ∀ i < 56, a ≠ (sp - 16#64) + BitVec.ofNat 64 i) :
    (Mem.storeInt m sp 8 value).get? a = m.get? a := by
  simpa only [BitVec.add_zero] using work_store_frame m sp a 0#64 value (by decide) outside

theorem compare_work_frame (s : MachineData) (pointer payload : BitVec 64) (a : BitVec 64)
    (outside : ∀ i < 56, a ≠ (s.regs.rsp.toBitVec - 16#64) + BitVec.ofNat 64 i) :
    (compareMem s pointer payload).get? a = s.dmem.get? a := by
  unfold compareMem
  rw [work_zero_frame _ s.regs.rsp.toBitVec a _ outside]
  simp (disch := first | exact outside | decide) only [work_store_frame]

theorem call_work_frame (s : MachineData) (base : Int64) (a : BitVec 64)
    (outside : ∀ i < 56, a ≠ (s.regs.rsp.toBitVec - 16#64) + BitVec.ofNat 64 i) :
    (callState s base).dmem.get? a = s.dmem.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  have inside : i < 8 := by simpa only [Int.toBytes_length] using hi
  have address : s.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 i =
      (s.regs.rsp.toBitVec - 16#64) + BitVec.ofNat 64 (8+i) := by bv_omega
  rw [address]
  exact outside (8+i) (by omega)

private theorem local_load_apart (m : DataMem) (sp a b : BitVec 64) (value : Int)
    (ha : a.toNat + 8 ≤ 40) (hb : b.toNat + 8 ≤ 40)
    (apart : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    Mem.loadInt (Mem.storeInt m (sp+b) 8 value) (sp+a) 8 = Mem.loadInt m (sp+a) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

private theorem local_zero_load_apart (m : DataMem) (sp a : BitVec 64) (value : Int)
    (lo : 8 ≤ a.toNat) (hi : a.toNat + 8 ≤ 40) :
    Mem.loadInt (Mem.storeInt m sp 8 value) (sp+a) 8 = Mem.loadInt m (sp+a) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i inside j stored
  bv_omega

theorem compare_spill_loads (s : MachineData) (pointer payload : BitVec 64) :
    Mem.loadInt (compareMem s pointer payload) s.regs.rsp.toBitVec 8 = some (payload.toNat : Int) ∧
    Mem.loadInt (compareMem s pointer payload) (s.regs.rsp.toBitVec + 8#64) 8 = some (pointer.toNat : Int) ∧
    Mem.loadInt (compareMem s pointer payload) (s.regs.rsp.toBitVec + 16#64) 8 = some (s.regs.rdx.toNat : Int) ∧
    Mem.loadInt (compareMem s pointer payload) (s.regs.rsp.toBitVec + 24#64) 8 = some (s.regs.rdi.toNat : Int) ∧
    Mem.loadInt (compareMem s pointer payload) (s.regs.rsp.toBitVec + 32#64) 8 = some (s.regs.r14.toNat : Int) := by
  refine ⟨stored_word_load _ _ _, ?_, ?_, ?_, ?_⟩
  all_goals
    simp (disch := decide) only [compareMem, local_zero_load_apart, local_load_apart]
  all_goals exact stored_word_load _ _ _

theorem call_local_load (m : DataMem) (sp distance : BitVec 64) (value : Int)
    (within : distance.toNat + 8 ≤ 40) :
    Mem.loadInt (Mem.storeInt m (sp - 8) 8 value) (sp + distance) 8 =
      Mem.loadInt m (sp + distance) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

theorem compare_mapped (s : MachineData) (pointer payload base : BitVec 64) (count : Nat)
    (hm : Large.Mapped s.dmem base count) : Large.Mapped (compareMem s pointer payload) base count := by
  unfold compareMem
  repeat' first | exact hm | apply Large.mapped_store

theorem call_mapped (s : MachineData) (base : Int64) (pointer : BitVec 64) (count : Nat)
    (hm : Large.Mapped s.dmem pointer count) : Large.Mapped (callState s base).dmem pointer count := by
  exact Large.mapped_store _ _ _ _ _ _ hm

end SszX86.Delimited
