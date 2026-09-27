import SszX86.NatAddMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Exact successful-buffer geometry without a signed bound on arena capacity. -/
theorem allocation_bounds (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
      address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length =
        address.toNat + r.used ∧
      r.used ≤ capacity.toNat ∧
      r.pointer + 8 * (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length ≤
        2^64 := by
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have exactAllocation := SszNative.NatAdd.allocation_exact left right address.toNat capacity.toNat used.toNat r allocated
  obtain ⟨checks, pointer, finish, length⟩ := geometry
  have positive : 0 < (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length := by
    rw [length]
    split <;> omega
  have cursor := Arena.used_le_start address.toNat used.toNat
  have storage := owned.arena_bound
  have startPointer := Arena.start_pointer address.toNat used.toNat
  have aligned := Arena.aligned_mod (address.toNat + used.toNat)
  have capacityPositive : 0 < capacity.toNat := by
    have fits := checks.2.2.2.2.2
    unfold Arena.finish at fits
    omega
  have basePositive := owned.arena_nonzero capacityPositive
  rw [exactAllocation.1] at finish
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [pointer, startPointer]
    exact aligned
  · omega
  · rw [pointer, finish]
    simp only [Arena.finish, Nat.add_assoc]
  · rw [finish]
    exact checks.2.2.2.2.2
  · rw [pointer]
    have fits := checks.2.2.2.2.2
    unfold Arena.finish at fits
    omega

theorem preserves_region (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (p n : Nat) (hp : Protected s address capacity used p n) :
    ∀ i < n, m.get? (BitVec.ofNat 64 (p+i)) = s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i inside
  have bound : p+i < 2^64 := by have := hp.bound; omega
  apply frame
  · have apart := hp.output
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · have apart := hp.activation
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · intro r allocated
    have apartCursor := hp.cursor
    have apartArena := hp.arena
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    constructor <;> omega

theorem preserves_load (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (p n off count : Nat) (hp : Protected s address capacity used p n)
    (inside : off + count ≤ n) :
    widthLoad m (p + off) count = widthLoad s.dmem (p + off) count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [Nat.add_assoc] using
    preserves_region s left right address capacity used ra owned m frame p n hp
      (off+i) (by omega)

/-- Preserve the complete supplied Large, not merely its significant prefix. -/
theorem operand_preserved (s : MachineData) (left right operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (stored : operand.At (widthLoad s.dmem))
    (hp : OperandProtected s address capacity used operand) :
    operand.At (widthLoad m) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [preserves_load s left right address capacity used ra owned m frame
      pointer.toNat (8 * words.length) (8 * i.val) 8 hp (by omega)]
    exact limbs i

end SszX86.NatAdd
