import SszX86.NatFromU128Memory
import SszX86.DelimitedWorkMemory

namespace SszX86.NatFromU128
open SszNative UintCodec BoolCodec
open NatToU128 (ByteFrame narrow_load_preserved narrow_width_preserved)

/-- Commit preserves any physical read outside the actual cursor/payload writes. -/
theorem commit_load_preserved (m : DataMem) (arena pointer finish low high : BitVec 64)
    (p count : Nat) (bound : p + count ≤ 2^64)
    (headerBound : arena.toNat + 24 ≤ 2^64) (payloadBound : pointer.toNat + 16 ≤ 2^64)
    (header : Body.Apart p count (arena.toNat+16) 8)
    (payload : Body.Apart p count pointer.toNat 16) :
    Mem.loadInt (commitMem m arena pointer finish low high) (BitVec.ofNat 64 p) count =
      Mem.loadInt m (BitVec.ofNat 64 p) count := by
  apply memmove_loadInt_congr
  intro i hi
  apply commit_frame
  · intro j hj
    simp only [Body.Apart] at header
    bv_omega
  · intro j hj
    simp only [Body.Apart] at payload
    bv_omega

theorem commit_width_preserved (m : DataMem) (arena pointer finish low high : BitVec 64)
    (p count : Nat) (bound : p + count ≤ 2^64)
    (headerBound : arena.toNat + 24 ≤ 2^64) (payloadBound : pointer.toNat + 16 ≤ 2^64)
    (header : Body.Apart p count (arena.toNat+16) 8)
    (payload : Body.Apart p count pointer.toNat 16) :
    widthLoad (commitMem m arena pointer finish low high) p count = widthLoad m p count := by
  unfold widthLoad
  rw [commit_load_preserved m arena pointer finish low high p count bound headerBound payloadBound header payload]

theorem commit_words (m : DataMem) (arena pointer finish low high : BitVec 64)
    (bound : pointer.toNat + 16 ≤ 2^64) :
    NatMemory.wordsAt (widthLoad (commitMem m arena pointer finish low high)) pointer.toNat [low, high] := by
  have stored := Large.fill_wordsAt (Mem.storeInt m (arena+16#64) 8 finish.toInt)
    pointer [low, high] (by simpa using bound)
  simpa only [commitMem, Large.fillMem, Nat.mul_zero, Nat.zero_add, Nat.reduceMul,
    BitVec.add_zero] using stored

theorem commit_cursor (m : DataMem) (arena pointer finish low high : BitVec 64)
    (headerBound : arena.toNat + 24 ≤ 2^64) (payloadBound : pointer.toNat + 16 ≤ 2^64)
    (apart : Body.Apart arena.toNat 24 pointer.toNat 16) :
    widthLoad (commitMem m arena pointer finish low high) (arena.toNat+16) 8 = some finish.toNat := by
  have lowApart (m : DataMem) : Mem.loadInt (Mem.storeInt m pointer 8 low.toInt) (arena+16#64) 8 =
      Mem.loadInt m (arena+16#64) 8 := by
    apply load_store_disjoint
    intro i hi j hj
    simp only [Body.Apart] at apart
    bv_omega
  have highApart (m : DataMem) : Mem.loadInt (Mem.storeInt m (pointer+8#64) 8 high.toInt) (arena+16#64) 8 =
      Mem.loadInt m (arena+16#64) 8 := by
    apply load_store_disjoint
    intro i hi j hj
    simp only [Body.Apart] at apart
    bv_omega
  simp only [commitMem, widthLoad, width_address]
  rw [highApart, lowApart, Delimited.stored_word_load]
  rfl

theorem result_model_small (address capacity used : BitVec 64) (wide : BitVec 128)
    (small : wide.toNat < 2^64) :
    outcome address capacity used wide = NatArithmetic.unchanged used.toNat (.ok (.small (wide.setWidth 64))) := by
  simp only [outcome, NatArithmetic.fromWide, small, ↓reduceIte]

theorem result_model_failure (address capacity used : BitVec 64) (wide : BitVec 128)
    (large : ¬ wide.toNat < 2^64)
    (failed : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none) :
    outcome address capacity used wide = NatArithmetic.unchanged used.toNat (.error .scratchExhausted) := by
  simp only [outcome, NatArithmetic.fromWide, large, ↓reduceIte, failed]

theorem result_model_success (address capacity used : BitVec 64) (wide : BitVec 128)
    (large : ¬ wide.toNat < 2^64) (r : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    outcome address capacity used wide =
      { result := .ok (.large (BitVec.ofNat 64 r.pointer) [wide.setWidth 64, (wide >>> 64).setWidth 64])
        used := r.used, allocation := some r, written := [wide.setWidth 64, (wide >>> 64).setWidth 64] } := by
  have high : (wide >>> 64).setWidth 64 ≠ 0#64 := fun h => large ((wide_small_iff wide).2 h)
  simp only [outcome, NatArithmetic.fromWide, large, ↓reduceIte, reserved, NatArithmetic.committed]
  simp [NatOperand.fromWords, Limbs.trim, high]

/-- Both complete limbs remain observable after result publication. -/
theorem result_written (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra)
    (r : SszNative.Arena.Reservation)
    (allocated : (outcome address capacity used wide).allocation = some r) :
    (NatOperand.large (BitVec.ofNat 64 r.pointer) (outcome address capacity used wide).written).At
      (widthLoad (resultMem s address capacity used wide)) := by
  by_cases small : wide.toNat < 2^64
  · rw [result_model_small address capacity used wide small] at allocated
    cases allocated
  cases reserve : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    rw [result_model_failure address capacity used wide small reserve] at allocated
    cases allocated
  | some reservation =>
    rw [result_model_success address capacity used wide small reservation reserve] at allocated
    have same : reservation = r := Option.some.inj allocated
    subst r
    have geometry := reserve_geometry s wide address capacity used ra owned reservation reserve
    have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
      Nat.mod_eq_of_lt (by omega)
    have stored := commit_words s.dmem s.regs.rcx.toBitVec (BitVec.ofNat 64 reservation.pointer)
      (BitVec.ofNat 64 reservation.used) (wide.setWidth 64) ((wide >>> 64).setWidth 64)
      (by rw [pointerNat]; omega)
    rw [result_model_success address capacity used wide small reservation reserve]
    simp only [resultMem, small, ↓reduceIte, reserve, NatOperand.At, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, pointerNat]
    refine ⟨geometry.1, geometry.2.1, geometry.2.2.2.2.2.1, ?_⟩
    intro i
    have within := i.isLt
    have frame := (publication_frame
      (commitMem s.dmem s.regs.rcx.toBitVec (BitVec.ofNat 64 reservation.pointer)
        (BitVec.ofNat 64 reservation.used) (wide.setWidth 64) ((wide >>> 64).setWidth 64))
      s.regs.rdi.toBitVec (BitVec.ofNat 64 reservation.pointer) 2 owned.output_bound).1
    rw [narrow_width_preserved _ _ _ _ (reservation.pointer+8*i.val) 8 frame
      (by simp only [List.length_cons, List.length_nil] at within; omega) (by
        have apart := owned.free_output
        simp only [Body.Apart, UInt64.toNat_toBitVec] at apart ⊢
        simp only [List.length_cons, List.length_nil] at within
        omega)]
    simpa only [pointerNat] using stored i

theorem result_observed (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra) :
    NatArithmetic.AddResultAt (widthLoad (resultMem s address capacity used wide))
      s.regs.rdi.toNat (outcome address capacity used wide).result := by
  have stored : ∀ result, (outcome address capacity used wide).result = .ok result →
      result.At (widthLoad (resultMem s address capacity used wide)) := by
    intro result success
    exact NatArithmetic.fromWide_result_at _ _ _ _ _ result success
      (result_written s wide address capacity used ra owned)
  by_cases small : wide.toNat < 2^64
  · have model := result_model_small address capacity used wide small
    rw [model]
    have observations := NatAdd.success_reads s.dmem s.regs.rdi.toBitVec 0 (wide.setWidth 64)
    simpa [resultMem, small, NatArithmetic.unchanged, NatArithmetic.AddResultAt,
      NatArithmetic.operandAt, NatOperand.pointer, NatOperand.payload, NatOperand.At, successMem] using
      And.intro (And.intro observations.1 (And.intro observations.2.1 True.intro)) observations.2.2
  cases reserve : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    rw [result_model_failure address capacity used wide small reserve]
    simpa [resultMem, small, reserve, NatArithmetic.unchanged,
      NatArithmetic.AddResultAt, errorMem] using NatAdd.error_reads s.dmem s.regs.rdi.toBitVec
  | some r =>
    have model := result_model_success address capacity used wide small r reserve
    have physical := stored _ (by rw [model])
    rw [model]
    have observations := NatAdd.success_reads
      (commitMem s.dmem s.regs.rcx.toBitVec (BitVec.ofNat 64 r.pointer) (BitVec.ofNat 64 r.used)
        (wide.setWidth 64) ((wide >>> 64).setWidth 64))
      s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer) 2
    simpa [resultMem, small, reserve, NatArithmetic.AddResultAt,
      NatArithmetic.operandAt, NatOperand.pointer, NatOperand.payload, successMem] using
      And.intro (And.intro observations.1 (And.intro observations.2.1 physical)) observations.2.2

end SszX86.NatFromU128
