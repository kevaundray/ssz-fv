import SszX86.DelimitedStack

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Fixed-distance stack stores cannot alter a distinct saved-register word. -/
theorem stack_load_apart (m : DataMem) (sp : BitVec 64) (a b : Nat) (value : Int)
    (ha : a ≤ 104) (hb : b ≤ 104) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) :
    Mem.loadInt (Mem.storeInt m (sp - BitVec.ofNat 64 b) 8 value)
      (sp - BitVec.ofNat 64 a) 8 = Mem.loadInt m (sp - BitVec.ofNat 64 a) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

/-- These facts are derived from the real PUSH stores, not supplied by the caller. -/
theorem pushed_saved (s : MachineData) :
    SavedAt (pushedMem s) (s.regs.rsp.toBitVec - 88) s := by
  have address (a : Nat) (ha : a ≤ 88) :
      s.regs.rsp.toBitVec - 88 + BitVec.ofNat 64 a =
        s.regs.rsp.toBitVec - BitVec.ofNat 64 (88-a) := by bv_omega
  constructor
  all_goals
    simp (disch := decide) only [address, Nat.reduceSub]
    simp (disch := first | decide | omega) only
      [pushedMem, BitVec.ofNat_eq_ofNat, stack_load_apart,
        BoolCodec.load_store_same, Nat.reduceMul]

/-- Pointwise stack frame, including the temporary lower BSR save area. -/
theorem stack_store_frame (m : DataMem) (sp a : BitVec 64)
    (distance count : Nat) (value : Int) (hoff : distance ≤ 104) (hcount : count ≤ distance)
    (outside : ∀ i < 104, a ≠ (sp - 104) + BitVec.ofNat 64 i) :
    (Mem.storeInt m (sp - BitVec.ofNat 64 distance) count value).get? a = m.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  have index : i < count := by simpa only [Int.toBytes_length] using hi
  have eq : sp - BitVec.ofNat 64 distance + BitVec.ofNat 64 i =
      (sp - 104) + BitVec.ofNat 64 (104-distance+i) := by bv_omega
  rw [eq]
  exact outside (104-distance+i) (by omega)

theorem pushed_frame (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 104, a ≠ (s.regs.rsp.toBitVec - 104) + BitVec.ofNat 64 i) :
    (pushedMem s).get? a = s.dmem.get? a := by
  simp (disch := first | assumption | decide | omega) only
    [pushedMem, BitVec.ofNat_eq_ofNat, stack_store_frame]

end SszX86.Delimited
