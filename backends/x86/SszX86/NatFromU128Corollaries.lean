import SszX86.NatFromU128Proofs
import SszX86.NatFromU128Small

namespace SszX86.NatFromU128
open SszNative UintCodec

/-- With no allocation, the cursor and every non-result byte are read-only. -/
theorem Frame.no_allocation {s : MachineData} {m : DataMem}
    {address capacity used : BitVec 64} {wide : BitVec 128}
    (frame : Frame s m address capacity used wide)
    (none : (outcome address capacity used wide).allocation = none)
    (a : BitVec 64) (outside : Body.Outside a.toNat s.regs.rdi.toNat 68) :
    m.get? a = s.dmem.get? a := by
  apply frame a
  · cases result : (outcome address capacity used wide).result with
    | error failure => exact outside
    | ok operand =>
      unfold Body.Outside at outside ⊢
      constructor <;> omega
  · intro r allocated
    rw [none] at allocated
    cases allocated

/-- Small keeps the exact original cursor and has no writable arena footprint. -/
theorem Post.small_resources {s : MachineData} {wide : BitVec 128}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s wide address capacity used ra t) (small : wide.toNat < 2^64) :
    (outcome address capacity used wide).allocation = none ∧
    (outcome address capacity used wide).written = [] ∧
    widthLoad t.1.dmem (s.regs.rcx.toNat+16) 8 = some used.toNat ∧
    ∀ a : BitVec 64, Body.Outside a.toNat s.regs.rdi.toNat 68 → t.1.dmem.get? a = s.dmem.get? a := by
  have model := result_model_small address capacity used wide small
  have none : (outcome address capacity used wide).allocation = none := by rw [model]; rfl
  refine ⟨none, by rw [model]; rfl, ?_, post.frame.no_allocation none⟩
  simpa only [model, NatArithmetic.unchanged] using post.cursor

/-- Any overflow/alignment/capacity rejection preserves the entry cursor and
all non-result storage; the complete private scratch-exhausted payload is live. -/
theorem Post.failure_resources {s : MachineData} {wide : BitVec 128}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s wide address capacity used ra t) (large : ¬ wide.toNat < 2^64)
    (failed : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none) :
    NatArithmetic.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat .scratchExhausted ∧
    widthLoad t.1.dmem (s.regs.rcx.toNat+16) 8 = some used.toNat ∧
    ∀ a : BitVec 64, Body.Outside a.toNat s.regs.rdi.toNat 68 → t.1.dmem.get? a = s.dmem.get? a := by
  have model := result_model_failure address capacity used wide large failed
  have none : (outcome address capacity used wide).allocation = none := by rw [model]; rfl
  refine ⟨?_, ?_, post.frame.no_allocation none⟩
  · simpa only [model, NatArithmetic.unchanged, NatArithmetic.AddResultAt] using post.observed
  · simpa only [model, NatArithmetic.unchanged] using post.cursor

/-- Success exposes Large(pointer,2), both complete words, and the exact cursor,
including consumed alignment padding. This is a consequence, not a run premise. -/
theorem Post.success_resources {s : MachineData} {wide : BitVec 128}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s wide address capacity used ra t) (large : ¬ wide.toNat < 2^64)
    (r : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (.large (BitVec.ofNat 64 r.pointer) [wide.setWidth 64, (wide >>> 64).setWidth 64]) ∧
    widthLoad t.1.dmem (s.regs.rdi.toNat+64) 4 = some 0 ∧
    widthLoad t.1.dmem (s.regs.rcx.toNat+16) 8 = some r.used ∧
    r.pointer = SszNative.Arena.aligned (address.toNat+used.toNat) ∧
    r.used = SszNative.Arena.start address.toNat used.toNat + 16 := by
  have model := result_model_success address capacity used wide large r reserved
  have observed := post.observed
  have cursor := post.cursor
  rw [model] at observed cursor
  obtain ⟨checks, fields⟩ :=
    (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  refine ⟨observed.1, observed.2, cursor, ?_, ?_⟩
  · rw [fields]
    exact SszNative.Arena.start_pointer address.toNat used.toNat
  · rw [fields]
    rfl

end SszX86.NatFromU128
