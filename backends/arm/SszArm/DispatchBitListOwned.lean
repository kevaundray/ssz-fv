import SszArm.DispatchBitListMemory

namespace SszArm.DispatchBitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open Dispatch (bodySP entered)
open BitList (Variant optionAddress)

/-- The accepted body ownership is derived, never an entry premise. -/
theorem body_owned {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : BitList.Owned (entered s (dispatchKind kind)) kind limit data := by
  have resources := entered_resources owned
  have pointer := option_read owned 8 8 (by decide)
  have payload := option_read owned 16 8 (by decide)
  refine {
    length := ?_, inputBound := ?_, input := ?_, descriptorBound := ?_, descriptor := entered_descriptor owned,
    outputBound := ?_, stackLow := ?_, stackHigh := ?_, outputStack := ?_, arenaBound := ?_,
    arenaStorage := ?_, arenaUsed := ?_, arenaNonnull := ?_, arenaLocal := ?_, availableLocal := ?_,
    availableInput := ?_, availableDescriptor := ?_, availableLimbs := ?_, fresh := ?_,
    inputOwned := ?_, descriptorOwned := ?_, limbsOwned := ?_, activationOwned := ?_ }
  · simpa (config := {decide := true}) only [Dispatch.entered_reg] using owned.length
  · simpa (config := {decide := true}) only [Dispatch.entered_reg] using owned.inputBound
  · simpa (config := {decide := true}) only [Dispatch.entered_reg] using
      (entry_frame owned).bytes _ _ owned.inputBound ((save_covered s kind _).protected owned.inputOwned) owned.input
  · simpa (config := {decide := true}) only [Dispatch.entered_reg] using owned.descriptorBound
  · simpa (config := {decide := true}) only [Dispatch.entered_reg] using owned.outputBound
  · rw [Dispatch.entered_sp]
    have low := owned.stackLow
    unfold bodySP
    bv_omega
  · rw [Dispatch.entered_sp]
    have low := owned.stackLow
    unfold bodySP
    bv_omega
  · simpa (config := {decide := true}) only [Dispatch.entered_reg, Dispatch.entered_sp] using owned.outputStack
  · simpa only [Dispatch.entered_arena] using owned.arenaBound
  · simpa only [resources] using owned.arenaStorage
  · simpa only [resources] using owned.arenaUsed
  · simpa only [resources] using owned.arenaNonnull
  · rw [entered_locals, Dispatch.entered_arena]
    exact (cons_covered _ _).protected owned.arenaLocal
  · simpa only [entered_locals, Dispatch.entered_sp, Dispatch.entered_arena,
      BitList.availableSpan, resources, availableSpan] using owned.availableLocal
  · simpa (config := {decide := true}) only [Dispatch.entered_reg,
      BitList.availableSpan, resources, availableSpan] using owned.availableInput
  · simpa (config := {decide := true}) only [Dispatch.entered_reg,
      BitList.availableSpan, resources, availableSpan] using owned.availableDescriptor
  · intro cap capEq
    simpa only [BitList.availableSpan, resources, availableSpan, entered_option, pointer, payload] using
      owned.availableLimbs cap capEq
  · intro reservation allocated
    rw [resources] at allocated
    simpa only [entered_locals, Dispatch.entered_arena] using owned.fresh reservation allocated
  · simpa (config := {decide := true}) only [resources, entered_writes, Dispatch.entered_reg] using
      (body_covered s kind _).protected owned.inputOwned
  · simpa (config := {decide := true}) only [resources, entered_writes, Dispatch.entered_reg] using
      (body_covered s kind _).protected owned.descriptorOwned
  · intro cap capEq
    rw [resources, entered_writes, entered_option, pointer, payload]
    intro nonzero nonempty
    exact (body_covered s kind _).protected (owned.limbsOwned cap capEq nonzero nonempty)
  · intro kindEq
    simpa only [resources, entered_writes, Dispatch.entered_sp] using owned.activationOwned kindEq

theorem entered_outcome {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) :
    BitList.outcome (entered s (dispatchKind kind)) limit data = outcome s limit data := by
  simp only [BitList.outcome, outcome, entered_resources owned]

theorem entered_code {s : ArmState} {base : BitVec 64} (kind : Variant)
    (code : BitList.JointCodeAt s base) : BitList.JointCodeAt (entered s (dispatchKind kind)) base := by
  rcases code with ⟨body, delimited, compare⟩
  constructor
  · simpa only [BitList.CodeAt, Dispatch.entered_program] using body
  · simpa only [Delimited.CodeAt, Dispatch.entered_program] using delimited
  · simpa only [NatCompare.CodeAt, Dispatch.entered_program] using compare

end SszArm.DispatchBitList
