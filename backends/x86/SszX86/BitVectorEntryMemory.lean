import SszX86.BitVectorEntry
import SszX86.BitVectorMapping

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The two body stores followed by the actual division CALL's return word. -/
def divisionReady (s : MachineData) (length : NatOperand) (ra : BitVec 64) : MachineData :=
  callState (entryState s length) ra

theorem call_work_load (m : DataMem) (sp : BitVec 64) (p n : Nat) (value : Int)
    (low : 72 ≤ sp.toNat) (high : sp.toNat + 368 ≤ 2^64)
    (bound : p + n ≤ 2^64) (apart : Body.Apart p n (sp.toNat - 72) 296) :
    Mem.loadInt (Mem.storeInt m (sp - 8#64) 8 value) (BitVec.ofNat 64 p) n =
      Mem.loadInt m (BitVec.ofNat 64 p) n := by
  apply load_store_disjoint
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

theorem initial_load (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (p n : Nat) (bound : p + n ≤ 2^64) (apart : Body.Apart p n (workStart s) workSize) :
    Mem.loadInt (divisionReady s length ra).dmem (BitVec.ofNat 64 p) n =
      Mem.loadInt s.dmem (BitVec.ofNat 64 p) n := by
  change Mem.loadInt (Mem.storeInt (entryMem s) (s.regs.rsp.toBitVec - 8#64) 8 ra.toInt)
    (BitVec.ofNat 64 p) n = _
  rw [call_work_load _ _ p n _ owned.stack_low owned.stack_bound bound apart]
  exact entry_load s saved length data address capacity used owned p n bound apart

theorem initial_width (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (p n : Nat) (bound : p + n ≤ 2^64) (apart : Body.Apart p n (workStart s) workSize) :
    widthLoad (divisionReady s length ra).dmem p n = widthLoad s.dmem p n := by
  unfold widthLoad
  rw [initial_load s saved length data address capacity used ra owned p n bound apart]

theorem initial_offset_load (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (p : BitVec 64) (size off count : Nat) (bound : p.toNat + size ≤ 2^64)
    (apart : Body.Apart p.toNat size (workStart s) workSize) (within : off + count ≤ size) :
    Mem.loadInt (divisionReady s length ra).dmem (p + BitVec.ofNat 64 off) count =
      Mem.loadInt s.dmem (p + BitVec.ofNat 64 off) count := by
  have result := initial_load s saved length data address capacity used ra owned
    (p.toNat + off) count (by omega) (by unfold Body.Apart at *; omega)
  simpa only [width_address] using result

theorem initial_operand (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    length.At (widthLoad (divisionReady s length ra).dmem) := by
  have stored := owned.descriptor.2.2
  cases length with
  | small limb => trivial
  | large p limbs =>
    obtain ⟨positive, aligned, bound, words⟩ := stored
    have protection := owned.operand_owned
    change Protected s address capacity used p.toNat (8 * limbs.length) at protection
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [initial_width s saved (.large p limbs) data address capacity used ra owned
      (p.toNat + 8 * i.val) 8 (by have := i.isLt; omega)
      (by have apart := protection.work; have := i.isLt; unfold Body.Apart at *; omega)]
    exact words i

theorem initial_mapped (s : MachineData) (length : NatOperand) (ra : BitVec 64) :
    Mapping.Extends s.dmem (divisionReady s length ra).dmem := by
  intro p n hm
  unfold divisionReady callState NatDivision.callState entryState entryMem
  repeat' first | exact hm | apply Large.mapped_store

/-- Restrict a physical mapping without changing its byte-wise meaning. -/
theorem mapped_subrange (m : DataMem) (p : BitVec 64) (total off count : Nat)
    (hm : Large.Mapped m p total) (within : off + count ≤ total) :
    Large.Mapped m (p + BitVec.ofNat 64 off) count := by
  intro i hi
  simpa only [memmove_addr_add] using hm (off + i) (by omega)

end SszX86.BitVector
