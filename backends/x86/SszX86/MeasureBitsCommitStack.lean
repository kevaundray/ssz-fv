import SszX86.MeasureBitsSpills

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem commit_stack_load (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (m : DataMem) (r : Arena.Reservation) (wide : BitVec 128)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (off byteCount : Nat) (within : off + byteCount ≤ 216) :
    Mem.loadInt (vectorCommitMem {s with dmem := m} r wide)
      (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) byteCount =
      Mem.loadInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) byteCount := by
  have geometry := reserve_geometry s desc value buffer address capacity used owned r reserved
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
  have headerApart := body_stack_header_apart s desc value buffer address capacity used owned
  have freeApart := owned.freeStack
  have stackLow := owned.stackLow
  have stackBound := owned.stackBound
  have keep := NatFromU128.commit_load_preserved m s.regs.rcx.toBitVec
    (BitVec.ofNat 64 r.pointer) (BitVec.ofNat 64 r.used) (wide.setWidth 64) ((wide >>> 64).setWidth 64)
    (s.regs.rsp.toNat + off) byteCount (by omega) owned.headerBound
    (by rw [pointerNat]; exact geometry.2.2.2.2.2.1)
    (by simp only [UInt64.toNat_toBitVec]; unfold Body.Apart at headerApart ⊢; omega)
    (by rw [pointerNat]; unfold Body.Apart at freeApart ⊢; omega)
  simpa only [vectorCommitMem, ← UInt64.toNat_toBitVec, width_address] using keep

theorem cursor_spill_disjoint (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used) :
    Large.Disjoint (s.regs.rcx.toBitVec + 16) (s.regs.rsp.toBitVec + 16) 8 8 := by
  intro i hi j hj equal
  apply owned.headerStack (16 + i) (by omega) (32 + j) (by omega)
  have left : s.regs.rcx.toBitVec + BitVec.ofNat 64 (16 + i) =
      s.regs.rcx.toBitVec + 16 + BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    with_unfolding_all rfl
  have right : s.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 (32 + j) =
      s.regs.rsp.toBitVec + 16 + BitVec.ofNat 64 j := by
    rw [BitVec.ofNat_add]
    bv_omega
  rw [left, right]
  exact equal

end SszX86.Measure.Bits
