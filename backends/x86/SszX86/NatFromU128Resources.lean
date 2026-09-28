import SszX86.NatFromU128MemoryFacts

namespace SszX86.NatFromU128
open SszNative UintCodec BoolCodec
open NatToU128 (ByteFrame narrow_load_preserved narrow_width_preserved)

theorem result_load_preserved (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra)
    (p count : Nat) (bound : p + count ≤ 2^64)
    (output : Body.Apart p count s.regs.rdi.toNat 68)
    (header : Body.Apart p count (s.regs.rcx.toNat+16) 8)
    (free : Body.Apart p count (address.toNat+used.toNat) (capacity.toNat-used.toNat)) :
    Mem.loadInt (resultMem s address capacity used wide) (BitVec.ofNat 64 p) count =
      Mem.loadInt s.dmem (BitVec.ofNat 64 p) count := by
  by_cases small : wide.toNat < 2^64
  · simp only [resultMem, small, ↓reduceIte]
    exact narrow_load_preserved _ _ _ _ p count
      (publication_frame s.dmem s.regs.rdi.toBitVec 0 (wide.setWidth 64) owned.output_bound).1 bound output
  cases reserve : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    simp only [resultMem, small, ↓reduceIte, reserve]
    exact narrow_load_preserved _ _ _ _ p count
      (publication_frame s.dmem s.regs.rdi.toBitVec 0 0 owned.output_bound).2 bound output
  | some r =>
    have geometry := reserve_geometry s wide address capacity used ra owned r reserve
    have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
    simp only [resultMem, small, ↓reduceIte, reserve]
    rw [narrow_load_preserved _ _ _ _ p count
      (publication_frame _ s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer) 2 owned.output_bound).1 bound output]
    apply commit_load_preserved _ _ _ _ _ _ p count bound owned.header_bound
    · rw [pointerNat]
      omega
    · exact header
    · rw [pointerNat]
      unfold Body.Apart at free ⊢
      omega

theorem result_width_preserved (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra)
    (p count : Nat) (bound : p + count ≤ 2^64)
    (output : Body.Apart p count s.regs.rdi.toNat 68)
    (header : Body.Apart p count (s.regs.rcx.toNat+16) 8)
    (free : Body.Apart p count (address.toNat+used.toNat) (capacity.toNat-used.toNat)) :
    widthLoad (resultMem s address capacity used wide) p count = widthLoad s.dmem p count := by
  unfold widthLoad
  rw [result_load_preserved s wide address capacity used ra owned p count bound output header free]

theorem result_return (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra) :
    Mem.loadInt (resultMem s address capacity used wide) s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  have same := result_load_preserved s wide address capacity used ra owned s.regs.rsp.toNat 8
    owned.return_bound owned.output_return.symm owned.cursor_return.symm owned.free_return.symm
  simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq, owned.return_load] using same

theorem result_header (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra) :
    widthLoad (resultMem s address capacity used wide) s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad (resultMem s address capacity used wide) (s.regs.rcx.toNat+8) 8 = some capacity.toNat := by
  have headerBound := owned.header_bound
  have out := owned.output_header
  have free := owned.free_header
  constructor
  · rw [result_width_preserved s wide address capacity used ra owned s.regs.rcx.toNat 8
      (by omega) (by unfold Body.Apart at *; omega) (by unfold Body.Apart; omega)
      (by unfold Body.Apart at *; omega)]
    simp only [widthLoad, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      owned.header.address_load, Option.map_some, Int.toNat_natCast]
  · rw [result_width_preserved s wide address capacity used ra owned (s.regs.rcx.toNat+8) 8
      (by omega) (by unfold Body.Apart at *; omega) (by unfold Body.Apart; omega)
      (by unfold Body.Apart at *; omega)]
    simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
      owned.header.capacity_load, Option.map_some, Int.toNat_natCast]

theorem result_cursor (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra) :
    widthLoad (resultMem s address capacity used wide) (s.regs.rcx.toNat+16) 8 =
      some (outcome address capacity used wide).used := by
  have bound := owned.header_bound
  have apart := owned.output_header
  have cursorOut : Body.Apart (s.regs.rcx.toNat+16) 8 s.regs.rdi.toNat 68 := by
    unfold Body.Apart at *
    omega
  have old : widthLoad s.dmem (s.regs.rcx.toNat+16) 8 = some used.toNat := by
    simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
      owned.header.used_load, Option.map_some, Int.toNat_natCast]
  by_cases small : wide.toNat < 2^64
  · rw [result_model_small address capacity used wide small]
    simp only [resultMem, small, ↓reduceIte, NatArithmetic.unchanged]
    rw [narrow_width_preserved _ _ _ _ (s.regs.rcx.toNat+16) 8
      (publication_frame _ s.regs.rdi.toBitVec 0 (wide.setWidth 64) owned.output_bound).1
      (by omega) cursorOut]
    exact old
  cases reserve : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    rw [result_model_failure address capacity used wide small reserve]
    simp only [resultMem, small, ↓reduceIte, reserve, NatArithmetic.unchanged]
    rw [narrow_width_preserved _ _ _ _ (s.regs.rcx.toNat+16) 8
      (publication_frame _ s.regs.rdi.toBitVec 0 0 owned.output_bound).2 (by omega) cursorOut]
    exact old
  | some r =>
    have geometry := reserve_geometry s wide address capacity used ra owned r reserve
    have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
    rw [result_model_success address capacity used wide small r reserve]
    simp only [resultMem, small, ↓reduceIte, reserve]
    rw [narrow_width_preserved _ _ _ _ (s.regs.rcx.toNat+16) 8
      (publication_frame _ s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer) 2 owned.output_bound).1
      (by omega) cursorOut]
    have cursor := commit_cursor s.dmem s.regs.rcx.toBitVec (BitVec.ofNat 64 r.pointer)
      (BitVec.ofNat 64 r.used) (wide.setWidth 64) ((wide >>> 64).setWidth 64)
      (by simpa only [UInt64.toNat_toBitVec] using owned.header_bound)
      (by rw [pointerNat]; omega) (by
        rw [UInt64.toNat_toBitVec, pointerNat]
        have free := owned.free_header
        unfold Body.Apart at free ⊢
        omega)
    simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt geometry.2.2.2.2.2.2] using cursor

theorem result_frame (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra) :
    Frame s (resultMem s address capacity used wide) address capacity used wide := by
  intro a output allocation
  have pairAway (h : Body.Outside a.toNat s.regs.rdi.toNat 16) :
      ∀ i < 16, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
    intro i hi
    have bound := owned.output_bound
    rw [← UInt64.toNat_toBitVec] at bound h
    exact Body.outside_byte _ _ 16 i (by omega) h hi
  have statusAway (h : Body.Outside a.toNat (s.regs.rdi.toNat+64) 4) :
      ∀ i < 4, a ≠ s.regs.rdi.toBitVec + 64#64 + BitVec.ofNat 64 i := by
    intro i hi
    have bound := owned.output_bound
    rw [← UInt64.toNat_toBitVec] at bound h
    unfold Body.Outside at h
    bv_omega
  by_cases small : wide.toNat < 2^64
  · rw [result_model_small address capacity used wide small] at output
    simp only [NatArithmetic.unchanged] at output
    simp only [resultMem, small, ↓reduceIte]
    exact success_frame _ _ _ _ _ (pairAway output.1) (statusAway output.2)
  cases reserve : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    rw [result_model_failure address capacity used wide small reserve] at output
    simp only [NatArithmetic.unchanged] at output
    simp only [resultMem, small, ↓reduceIte, reserve]
    exact (publication_frame _ s.regs.rdi.toBitVec 0 0 owned.output_bound).2 a output
  | some r =>
    have geometry := reserve_geometry s wide address capacity used ra owned r reserve
    have model := result_model_success address capacity used wide small r reserve
    have outside := allocation r (by rw [model])
    rw [model] at output
    simp only at output
    simp only [resultMem, small, ↓reduceIte, reserve]
    rw [success_frame _ _ _ _ _ (pairAway output.1) (statusAway output.2)]
    apply commit_frame
    · intro i hi
      have bound := owned.header_bound
      have h := outside.1
      rw [← UInt64.toNat_toBitVec] at bound h
      unfold Body.Outside at h
      bv_omega
    · intro i hi
      have h := outside.2
      unfold Body.Outside at h
      bv_omega

structure Post (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (outcome address capacity used wide).result
  returned : Delimited.Returned s ra t
  memory : t.1.dmem = resultMem s address capacity used wide
  frame : Frame s t.1.dmem address capacity used wide
  header : widthLoad t.1.dmem s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.rcx.toNat+8) 8 = some capacity.toNat
  cursor : widthLoad t.1.dmem (s.regs.rcx.toNat+16) 8 = some (outcome address capacity used wide).used
  written : ∀ r, (outcome address capacity used wide).allocation = some r →
    (NatOperand.large (BitVec.ofNat 64 r.pointer) (outcome address capacity used wide).written).At (widthLoad t.1.dmem)

theorem post_of_memory (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra)
    (t : MachineState) (memory : t.1.dmem = resultMem s address capacity used wide)
    (returned : Delimited.Returned s ra t) : Post s wide address capacity used ra t := by
  refine ⟨?_, returned, memory, ?_, ?_, ?_, ?_⟩ <;> rw [memory]
  · exact result_observed s wide address capacity used ra owned
  · exact result_frame s wide address capacity used ra owned
  · exact result_header s wide address capacity used ra owned
  · exact result_cursor s wide address capacity used ra owned
  · exact result_written s wide address capacity used ra owned

end SszX86.NatFromU128
