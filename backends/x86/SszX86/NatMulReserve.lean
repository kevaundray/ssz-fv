import SszX86.NatMulReserveCount
import SszX86.NatMulReserveCommit
import SszX86.MeasureBitsStored

namespace SszX86.NatMul.Reservation
open SszNative
open UintCodec

/-- Initial ownership of the writable suffix and the 40-byte local frame plus
CALL's eight-byte return slot. The arena's used prefix is deliberately absent. -/
structure Storage (s : MachineData) (address capacity used : BitVec 64) : Prop where
  used_bound : used.toNat ≤ capacity.toNat
  free : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8#64) 48
  free_stack : Large.Disjoint (address + used) (s.regs.rsp.toBitVec - 8#64)
    (capacity.toNat - used.toNat) 48

/-- The success state is exactly the stores and real helper result. The failure
alternatives retain their actual, distinct dispatch PCs and unchanged memory. -/
def Post (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Failed s base address capacity used t ∨
  (total s < 2^64 ∧ ∃ r,
    Arena.reserve address.toNat capacity.toNat used.toNat (total s) = some r ∧
    ∃ guardFlags fillFlags,
      MemsetCall.Post (preparedState (allocatedState s address used guardFlags) fillFlags)
        (base + 493).toBitVec (8 * total s) t)

private theorem destination (s : MachineData) (address used : BitVec 64)
    (guardFlags fillFlags : StatusFlags) :
    (preparedState (allocatedState s address used guardFlags) fillFlags).regs.rdi.toBitVec =
      address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) := by
  simp [preparedState, allocatedState, reservedState, countState]

private theorem byte_count (s : MachineData) (address used : BitVec 64)
    (guardFlags fillFlags : StatusFlags) (bound : total s < 2^64) :
    (preparedState (allocatedState s address used guardFlags) fillFlags).regs.rdx.toBitVec =
      BitVec.ofNat 64 (8 * total s) := by
  simp only [preparedState, allocatedState, reservedState, counted_nat s s.status bound,
    UInt64.toBitVec_ofNat']

/-- Guards, cursor commit, stack spills, six-byte CALL and helper RET. The only
memory hypotheses describe bytes mapped before the allocation starts. -/
theorem runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemsetCall.MemsetCodeAt e (base + 148928))
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) (storage : Storage s address capacity used)
    (positive : 0 < total s) :
    Eventually (step e) (Post s base address capacity used) (s, base + 275) := by
  apply eventually_trans _ _ _ _ (checked_runs e base hc s address capacity used header positive)
  intro t checked
  rcases checked with failed | ⟨bound, r, reserved, pc, guardFlags, state⟩
  · exact Eventually.done _ (Or.inl failed)
  · rcases t with ⟨t, pc'⟩
    dsimp only at pc state
    subst pc'
    subst t
    have natural := counted_nat s s.status bound
    have checks := (Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).mp reserved
    have fits := checks.1.2.2.2.2.2
    have startBound := checks.1.2.2.2.1
    have startLow := Arena.used_le_start address.toNat used.toNat
    have lengthBound : 8 * total s < 2^64 := by have := checks.1.1; omega
    have fits' : Arena.start address.toNat used.toNat + 8 * total s ≤ capacity.toNat := fits
    have freeOffset : used + BitVec.ofNat 64 (Arena.start address.toNat used.toNat - used.toNat) =
        BitVec.ofNat 64 (Arena.start address.toNat used.toNat) := by
      have word : used = BitVec.ofNat 64 used.toNat := by simp
      rw [word, ← BitVec.ofNat_add, Nat.add_sub_of_le startLow]
    have hm : Large.Mapped s.dmem
        (address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat)) (8 * total s) := by
      have sub := Delimited.Reservation.mapped_subrange s.dmem (address + used)
        (capacity.toNat - used.toNat) (Arena.start address.toNat used.toNat - used.toNat)
        (8 * total s) storage.free (by omega)
      simpa only [BitVec.add_assoc, freeOffset] using sub
    have stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 40 := by
      have sub := Delimited.Reservation.mapped_subrange s.dmem (s.regs.rsp.toBitVec - 8#64)
        48 8 40 storage.stack (by decide)
      simpa using sub
    have slot : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8#64) 8 := by
      exact fun i hi => storage.stack i (by omega)
    have arena := Measure.Bits.load_mapped s.dmem (s.regs.r9.toBitVec + 16#64) 8 _ header.used_load
    apply prepare_cps e base hc _ _ stack arena
    intro fillFlags
    have buffer := prepared_mapped (allocatedState s address used guardFlags) _ (8 * total s) hm
    have slot' := prepared_mapped (allocatedState s address used guardFlags) _ 8 slot
    have apart : Large.Disjoint
        (address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat))
        (s.regs.rsp.toBitVec - 8#64) (8 * total s) 8 := by
      intro i hi j hj
      have sep := storage.free_stack
        (Arena.start address.toNat used.toNat - used.toNat + i) (by omega) j (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc,
        BitVec.add_assoc address used, freeOffset] using sep
    have zero : (preparedState (allocatedState s address used guardFlags) fillFlags).regs.rsi = 0 := rfl
    have run := MemsetCall.runs e base hc helper
      (preparedState (allocatedState s address used guardFlags) fillFlags) (8 * total s)
      (byte_count s address used guardFlags fillFlags bound) zero lengthBound
      (by simpa only [destination] using buffer) slot'
      (by simpa only [destination] using apart)
    apply eventually_weaken (step e) _ _ _ _ run
    intro final post
    exact Or.inr ⟨bound, r, reserved, guardFlags, fillFlags, post⟩

/-- The allocating main branch is related to the checked model on both failure
and success, without assuming which resource branch is taken. -/
theorem large_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemsetCall.MemsetCodeAt e (base + 148928))
    (s : MachineData) (address capacity used : BitVec 64)
    (left right : NatOperand) (lc : s.regs.r12.toNat = left.wordCount)
    (rc : s.regs.r13.toNat = right.wordCount)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (header : Header s address capacity used) (storage : Storage s address capacity used) :
    Eventually (step e) (fun t =>
      (Failed s base address capacity used t ∧
        SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
          NatArithmetic.unchanged used.toNat (.error .scratchExhausted)) ∨
      ∃ r guardFlags fillFlags,
        SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
          NatArithmetic.committed r (SszNative.NatMul.writtenWords left right) ∧
        MemsetCall.Post (preparedState (allocatedState s address used guardFlags) fillFlags)
          (base + 493).toBitVec (8 * (left.wordCount + right.wordCount)) t)
      (s, base + 275) := by
  have counts : total s = left.wordCount + right.wordCount := by simp [total, lc, rc]
  have run := runs e base hc helper s address capacity used header storage (by rw [counts]; omega)
  apply eventually_weaken (step e) _ _ _ _ run
  intro t post
  rcases post with failed | ⟨bound, r, reserved, guardFlags, fillFlags, filled⟩
  · exact Or.inl ⟨failed, failed_model s base address capacity used left right lc rc hl hr t failed⟩
  · exact Or.inr ⟨r, guardFlags, fillFlags,
      reserved_model s address capacity used left right lc rc hl hr bound r reserved,
      by simpa only [counts] using filled⟩

end SszX86.NatMul.Reservation
