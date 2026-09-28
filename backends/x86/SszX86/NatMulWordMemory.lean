import SszX86.NatMulWordResources

namespace SszX86.NatMulWord
open SszNative UintCodec

def ResultOutside (result : Except NatArithmetic.Failure NatOperand) (out a : Nat) : Prop :=
  match result with
  | .ok _ => Body.Outside a out 16 ∧ Body.Outside a (out+64) 4
  | .error _ => Body.Outside a out 68

theorem ResultOutside.of_outside (result : Except NatArithmetic.Failure NatOperand)
    (out a : Nat) (outside : Body.Outside a out 72) : ResultOutside result out a := by
  cases result <;> simp only [ResultOutside] <;> unfold Body.Outside at * <;> omega

theorem preserves_region (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat))
    (p n : Nat) (hp : Protected s address capacity used p n) :
    ∀ i < n, m.get? (BitVec.ofNat 64 (p+i)) = s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i inside
  have bound : p+i < 2^64 := by have := hp.bound; omega
  apply frame
  · apply ResultOutside.of_outside
    have apart := hp.output
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
    have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    constructor <;> omega

theorem preserves_load (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat))
    (p n off count : Nat) (hp : Protected s address capacity used p n)
    (inside : off + count ≤ n) :
    widthLoad m (p + off) count = widthLoad s.dmem (p + off) count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [Nat.add_assoc] using
    preserves_region s operand factor address capacity used ra owned m frame p n hp
      (off+i) (by omega)

theorem operand_preserved (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)) :
    operand.At (widthLoad m) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := owned.operand_at
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [preserves_load s (.large pointer words) factor address capacity used ra owned m frame
      pointer.toNat (8 * words.length) (8 * i.val) 8 owned.operand_owned (by omega)]
    exact limbs i

theorem Frame.return_slot {s : MachineData} {operand : NatOperand}
    {factor address capacity used ra : BitVec 64} (owned : Owned s operand factor address capacity used ra)
    {m : DataMem} (frame : Frame s m
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have unchanged : Mem.loadInt m s.regs.rsp.toBitVec 8 = Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
    apply memmove_loadInt_congr
    intro i hi
    have bound := owned.return_bound
    have low := owned.stack_low
    have natural : (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rsp.toNat+i := by
      change s.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 at bound
      change (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rsp.toBitVec.toNat+i
      bv_omega
    apply frame
    · apply ResultOutside.of_outside
      rw [natural]
      have apart := owned.output_return
      unfold Body.Outside Body.Apart at *
      omega
    · rw [natural]
      unfold Body.Outside
      omega
    · intro r allocated
      rw [natural]
      have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
      have apartCursor := owned.cursor_return
      have apartArena := owned.arena_return
      have usedBound := owned.used_bound
      unfold Body.Outside Body.Apart at *
      constructor <;> omega
  exact unchanged.trans owned.return_load

end SszX86.NatMulWord
