import SszArm.HashMemory

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

def outputPtr (s : ArmState) : BitVec 64 := r (.GPR 0#5) s
def statePtr (s : ArmState) : BitVec 64 := r (.GPR 1#5) s
def stackTop (s : ArmState) : BitVec 64 := r (.GPR 31#5) s
def bodySP (s : ArmState) : BitVec 64 := stackTop s - 32#64

structure Geometry (s : ArmState) : Prop where
  stackLow : 192 ≤ (stackTop s).toNat
  stateBound : (statePtr s).toNat + 112 ≤ 2^64
  outputBound : (outputPtr s).toNat + 32 ≤ 2^64
  stateStack : (statePtr s).toNat + 112 ≤ (stackTop s).toNat - 192 ∨
    (stackTop s).toNat ≤ (statePtr s).toNat
  outputStack : (outputPtr s).toNat + 32 ≤ (stackTop s).toNat - 192 ∨
    (stackTop s).toNat ≤ (outputPtr s).toNat
  outputState : (outputPtr s).toNat + 32 ≤ (statePtr s).toNat ∨
    (statePtr s).toNat + 112 ≤ (outputPtr s).toNat

theorem geometry {s : ArmState} {base : BitVec 64} {value : StreamState}
    (owned : FinalizeOwned s base value) : Geometry s := by
  have stateApart := owned.stateStack.resolve_left (by decide)
  have outputApart := owned.outputStack.resolve_left (by decide)
  have resultApart := owned.outputState.resolve_left (by decide)
  refine ⟨owned.stackLow, owned.stateBound, owned.outputBound, ?_, ?_, ?_⟩
  · have h := stateApart (stackSpan s 192) (by simp)
    simpa only [stackSpan, statePtr, stackTop, Nat.sub_add_cancel owned.stackLow] using h
  · have h := outputApart (stackSpan s 192) (by simp)
    simpa only [stackSpan, outputPtr, stackTop, Nat.sub_add_cancel owned.stackLow] using h
  · exact resultApart ((r (.GPR 1#5) s).toNat, 112) (by simp)

theorem Geometry.bodySP_nat {s : ArmState} (g : Geometry s) :
    (bodySP s).toNat = (stackTop s).toNat - 32 := by
  have := g.stackLow
  unfold bodySP
  bv_omega

theorem Geometry.bodySP_low {s : ArmState} (g : Geometry s) :
    160 ≤ (bodySP s).toNat := by
  rw [g.bodySP_nat]
  have := g.stackLow
  omega

theorem Geometry.stack_subspan {s : ArmState} (g : Geometry s)
    (address : BitVec 64) (bytes : Nat)
    (lo : (stackTop s).toNat - 192 ≤ address.toNat)
    (hi : address.toNat + bytes ≤ (stackTop s).toNat) :
    ∃ outer ∈ finalizeWrites s, outer.1 ≤ address.toNat ∧
      address.toNat + bytes ≤ outer.1 + outer.2 := by
  refine ⟨stackSpan s 192, by simp [finalizeWrites], lo, ?_⟩
  change address.toNat + bytes ≤ (stackTop s).toNat - 192 + 192
  rw [Nat.sub_add_cancel g.stackLow]
  exact hi

theorem Geometry.state_subspan {s : ArmState} (_g : Geometry s)
    (address : BitVec 64) (bytes : Nat)
    (lo : (statePtr s).toNat ≤ address.toNat)
    (hi : address.toNat + bytes ≤ (statePtr s).toNat + 112) :
    ∃ outer ∈ finalizeWrites s, outer.1 ≤ address.toNat ∧
      address.toNat + bytes ≤ outer.1 + outer.2 := by
  exact ⟨((statePtr s).toNat, 112), by simp [finalizeWrites, statePtr], lo, hi⟩

theorem Geometry.output_subspan {s : ArmState} (_g : Geometry s)
    (address : BitVec 64) (bytes : Nat)
    (lo : (outputPtr s).toNat ≤ address.toNat)
    (hi : address.toNat + bytes ≤ (outputPtr s).toNat + 32) :
    ∃ outer ∈ finalizeWrites s, outer.1 ≤ address.toNat ∧
      address.toNat + bytes ≤ outer.1 + outer.2 := by
  exact ⟨((outputPtr s).toNat, 32), by simp [finalizeWrites, outputPtr], lo, hi⟩

theorem Geometry.state_stack {s : ArmState} (g : Geometry s)
    (address : BitVec 64) (bytes : Nat)
    (lo : (stackTop s).toNat - 192 ≤ address.toNat)
    (hi : address.toNat + bytes ≤ (stackTop s).toNat) :
    Protected [(address.toNat, bytes)] (statePtr s).toNat 112 := by
  right
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  have := g.stateStack
  simp only
  omega

theorem Geometry.saved_protected {s : ArmState} (g : Geometry s)
    (writes : List Span)
    (ranges : ∀ span ∈ writes,
      ((stackTop s).toNat - 192 ≤ span.1 ∧ span.1 + span.2 ≤ (bodySP s).toNat) ∨
      ((statePtr s).toNat ≤ span.1 ∧ span.1 + span.2 ≤ (statePtr s).toNat + 112) ∨
      ((outputPtr s).toNat ≤ span.1 ∧ span.1 + span.2 ≤ (outputPtr s).toNat + 32)) :
    Protected writes (bodySP s).toNat 32 := by
  right
  intro span member
  have h := ranges span member
  have hs := g.stateStack
  have ho := g.outputStack
  have hp := g.bodySP_nat
  have hl := g.stackLow
  omega

theorem Geometry.compression_contained {s t : ArmState} (g : Geometry s)
    (sp : r (.GPR 31#5) t = bodySP s)
    (state : r (.GPR 0#5) t = statePtr s + 64#64) :
    ∀ span ∈ compressionWrites t, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  intro span member
  simp only [compressionWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨stackSpan s 192, by simp [finalizeWrites], ?_, ?_⟩
    all_goals
      simp only [stackSpan, sp, g.bodySP_nat]
      have low := g.stackLow
      change 192 ≤ (r (.GPR 31#5) s).toNat at low
      unfold stackTop at *
      omega
  · have physical := g.stateBound
    have at64 : (statePtr s + 64#64).toNat = (statePtr s).toNat + 64 := by bv_omega
    simpa only [state, at64] using g.state_subspan (statePtr s + 64#64) 32
      (by rw [at64]; omega) (by rw [at64]; omega)

theorem protected_narrow_writes {small large : List Span} {address count : Nat}
    (owned : Protected large address count)
    (contained : ∀ span ∈ small, ∃ outer ∈ large,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2) :
    Protected small address count := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    obtain ⟨outer, outerMember, lo, hi⟩ := contained span member
    have apart := separate outer outerMember
    omega

theorem Geometry.compression_saved {s t : ArmState} (g : Geometry s)
    (sp : r (.GPR 31#5) t = bodySP s)
    (state : r (.GPR 0#5) t = statePtr s + 64#64) :
    Protected (compressionWrites t) (bodySP s).toNat 32 := by
  apply g.saved_protected
  intro span member
  simp only [compressionWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  have physical := g.stateBound
  have low := g.stackLow
  have spNat := g.bodySP_nat
  rcases member with rfl | rfl
  · left
    simp only [stackSpan, sp]
    omega
  · right; left
    rw [state]
    constructor <;> bv_omega

theorem Geometry.compression_input {s t : ArmState} (g : Geometry s)
    (sp : r (.GPR 31#5) t = bodySP s)
    (state : r (.GPR 0#5) t = statePtr s + 64#64) :
    Protected (compressionWrites t) (statePtr s).toNat 64 := by
  right
  intro span member
  simp only [compressionWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  have physical := g.stateBound
  have low := g.stackLow
  have spNat := g.bodySP_nat
  have apart := g.stateStack
  rcases member with rfl | rfl
  · simp only [stackSpan, sp]
    omega
  · simp only [state]
    left
    bv_omega

theorem Geometry.compression_length {s t : ArmState} (g : Geometry s)
    (sp : r (.GPR 31#5) t = bodySP s)
    (state : r (.GPR 0#5) t = statePtr s + 64#64) :
    Protected (compressionWrites t) (statePtr s + 104#64).toNat 8 := by
  right
  intro span member
  simp only [compressionWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  have physical := g.stateBound
  have low := g.stackLow
  have spNat := g.bodySP_nat
  have apart := g.stateStack
  rcases member with rfl | rfl
  · simp only [stackSpan, sp]
    bv_omega
  · simp only [state]
    right
    bv_omega

end SszArm.Hash.Finalize
