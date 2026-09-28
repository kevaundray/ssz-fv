import SszX86.MeasureBitsConstructorCalls

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- Successful native construction borrows either no bytes or exactly the
allocation recorded by that same call. -/
theorem from_wide_borrowed (address capacity used : BitVec 64) (wide : BitVec 128)
    (actual : NatOperand)
    (success : (NatArithmetic.fromWide address.toNat capacity.toNat used.toNat wide).result = .ok actual)
    (a : BitVec 64) (borrowed : Emit.NatBorrowed actual a) :
    AllocationWrites [NatArithmetic.fromWide address.toNat capacity.toNat used.toNat wide] a := by
  change (NatFromU128.outcome address capacity used wide).result = .ok actual at success
  change AllocationWrites [NatFromU128.outcome address capacity used wide] a
  by_cases small : wide.toNat < 2^64
  · rw [NatFromU128.result_model_small address capacity used wide small] at success
    simp only [NatArithmetic.unchanged, Except.ok.injEq] at success
    subst actual
    exact False.elim borrowed
  cases reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    rw [NatFromU128.result_model_failure address capacity used wide small reserved] at success
    cases success
  | some r =>
    have model := NatFromU128.result_model_success address capacity used wide small r reserved
    rw [model] at success
    simp only [Except.ok.injEq] at success
    subst actual
    refine ⟨NatFromU128.outcome address capacity used wide, by simp only [List.mem_singleton], r, ?_, ?_⟩
    · rw [model]
    · simpa only [model, Emit.NatBorrowed] using borrowed

theorem allocation_output_disjoint (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (pointer byteCount : Nat)
    (lo : address.toNat + used.toNat ≤ pointer)
    (hi : pointer + byteCount ≤ address.toNat + capacity.toNat) :
    Large.Disjoint (BitVec.ofNat 64 pointer) s.regs.rbx.toBitVec byteCount 72 := by
  by_cases empty : byteCount = 0
  · subst byteCount
    intro i impossible
    omega
  have arenaBound := owned.arenaBound
  have pointerNat : (BitVec.ofNat 64 pointer).toNat = pointer := Nat.mod_eq_of_lt (by omega)
  apply Body.apart_bytes
  · rw [pointerNat]
    omega
  · simpa only [UInt64.toNat_toBitVec] using owned.resultBound
  · rw [pointerNat, UInt64.toNat_toBitVec]
    have separated := owned.freeResult
    unfold Body.Apart at separated ⊢
    omega

theorem publication_calls (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (before after : DataMem) (calls : List (NatArithmetic.Outcome NatOperand))
    (geometry : ∀ call ∈ calls, ∀ r, call.allocation = some r →
      address.toNat + used.toNat ≤ r.pointer ∧
        r.pointer + 8 * call.written.length ≤ address.toNat + capacity.toNat)
    (stored : CallsAt (widthLoad before) calls)
    (frame : MemoryFrame before after (fun a => InSpan a s.regs.rbx.toBitVec 72)) :
    CallsAt (widthLoad after) calls := by
  intro call member r allocated i
  have bounds := geometry call member r allocated
  have apart := allocation_output_disjoint s desc value buffer address capacity used owned
    r.pointer (8 * call.written.length) bounds.1 bounds.2
  have same := frame_load_window before after _ frame (BitVec.ofNat 64 r.pointer)
    (8 * i.val) 8 (8 * call.written.length) (by have hi := i.isLt; omega) (by
      rintro a ⟨j, hj, rfl⟩ ⟨k, hk, equal⟩
      exact apart j hj k hk equal)
  unfold widthLoad
  rw [BitVec.ofNat_add, same]
  simpa only [widthLoad, BitVec.ofNat_add] using stored call member r allocated i

theorem publication_operand (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (before after : DataMem) (calls : List (NatArithmetic.Outcome NatOperand))
    (geometry : ∀ call ∈ calls, ∀ r, call.allocation = some r →
      address.toNat + used.toNat ≤ r.pointer ∧
        r.pointer + 8 * call.written.length ≤ address.toNat + capacity.toNat)
    (operand : NatOperand)
    (borrows : ∀ a, Emit.NatBorrowed operand a → AllocationWrites calls a)
    (stored : operand.At (widthLoad before))
    (frame : MemoryFrame before after (fun a => InSpan a s.regs.rbx.toBitVec 72)) :
    operand.At (widthLoad after) := by
  apply operand_frame before after _ frame operand _ stored
  intro a borrowed
  obtain ⟨call, member, r, allocated, ⟨i, hi, rfl⟩⟩ := borrows a borrowed
  have bounds := geometry call member r allocated
  have apart := allocation_output_disjoint s desc value buffer address capacity used owned
    r.pointer (8 * call.written.length) bounds.1 bounds.2
  rintro ⟨j, hj, equal⟩
  exact apart i hi j hj equal

theorem publication_header (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (before after : DataMem)
    (frame : MemoryFrame before after (fun a => InSpan a s.regs.rbx.toBitVec 72))
    (off : Nat) (within : off + 8 ≤ 24) :
    widthLoad after (s.regs.rcx.toNat + off) 8 = widthLoad before (s.regs.rcx.toNat + off) 8 := by
  unfold widthLoad
  rw [← UInt64.toNat_toBitVec, width_address]
  congr 1
  apply frame_load_window before after _ frame s.regs.rcx.toBitVec off 8 24 within
  rintro a ⟨i, hi, rfl⟩ ⟨j, hj, equal⟩
  exact owned.resultHeader j hj i hi equal.symm

end SszX86.Measure.Bits
