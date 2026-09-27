import SszArm.NatAddSmallLoopControl
import SszArm.NatAddLoopMemory

namespace SszArm.NatAdd.SmallLoop

open UintCodec
open NatCompare (Source Words saved)
open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The loop owns only its remaining output suffix and the real lowering slot. -/
def writes (sp output : BitVec 64) (index remaining : Nat) : List Span :=
  [(sp.toNat - 16, 16), (output.toNat + 8 * index, 8 * remaining)]

/-- Physical extent and stack separation, with no signed-size restriction. -/
structure Layout (sp output : BitVec 64) (allocated : Nat) : Prop where
  stack : 16 ≤ sp.toNat
  physical : output.toNat + 8 * allocated ≤ 2^64
  separate : output.toNat + 8 * allocated ≤ sp.toNat - 16 ∨ sp.toNat ≤ output.toNat

def address (output : BitVec 64) (index : Nat) : BitVec 64 :=
  output + BitVec.ofNat 64 (8 * index)

theorem address_shift (output : BitVec 64) (index : Nat) :
    address output index = output + (BitVec.ofNat 64 index <<< 3) := by
  simp only [address]
  congr 1
  bv_omega

theorem address_nat {sp output : BitVec 64} {allocated index : Nat}
    (layout : Layout sp output allocated) (hi : index < allocated) :
    (address output index).toNat = output.toNat + 8 * index := by
  have := layout.physical
  unfold address
  bv_omega

def readonlyOps : List Op :=
  [.p1868, .p1872, .p1876, .p1912, .p1916, .p1952, .p1956, .p1960,
   .p1964, .p1968, .p1972, .p1976, .p1980, .p1984, .p1988, .p1992]

theorem readonly_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (regions : List Span) (hs : ∀ op ∈ ops, op ∈ readonlyOps) :
    LoopFrame regions s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact LoopFrame.refl regions s
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    have frame : LoopFrame regions s (op.effect base s) := by
      cases op <;> simp_all only [readonlyOps, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · intro a ha
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact frame.trans (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop)))

theorem read_frame (s : ArmState) (base sp output : BitVec 64)
    (right : List (BitVec 64)) (index remaining : Nat)
    (hsp : r (.GPR 31#5) s = sp) (hs : 16 ≤ sp.toNat) :
    LoopFrame (writes sp output index remaining) s (readState s base right index) := by
  have savedFrame := NatCompare.saved_frame s 9#5 (by simpa [hsp] using hs)
  by_cases present : index < right.length
  all_goals
    constructor
    · simp [readState, present, loadResult, saved, state_simp_rules]
    · simp [readState, present, loadResult, saved, state_simp_rules]
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [readState, present, loadResult, LoadKind.dst,
        LoadKind.tmp, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        saved, state_simp_rules]
    · intro reg
      simp [readState, present, loadResult, LoadKind.tmp, block, Op.effect,
        put, next, Udivti3.compare, Udivti3.next, saved, state_simp_rules]
    · intro a outside
      have slot := outside (sp.toNat - 16, 16) (by simp [writes])
      simp only [readState, present, ↓reduceIte, loadResult, LoadKind.tmp,
        block, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, ArmState.mem_w_eq_mem]
      first
      | exact savedFrame.memory a (by rw [hsp]; omega)
      | rfl

theorem tail_frame (s : ArmState) (base : BitVec 64) (regions : List Span) :
    LoopFrame regions s (tailState s base) := by
  apply readonly_frame
  intro op hop
  unfold tailOps at hop
  split at hop <;> simp_all [readonlyOps]

/-- Suffix composition enlarges an allowed span; it does not authorize padding
or any already-used arena bytes. -/
theorem widen_frame {s t : ArmState} (sp output : BitVec 64)
    (index remaining innerIndex innerRemaining : Nat)
    (low : index ≤ innerIndex) (high : innerIndex + innerRemaining ≤ index + remaining)
    (frame : LoopFrame (writes sp output innerIndex innerRemaining) s t) :
    LoopFrame (writes sp output index remaining) s t := by
  refine ⟨frame.program, frame.error, frame.registers, frame.vectors, ?_⟩
  intro a outside
  apply frame.memory a
  intro span member
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outside _ (by simp [writes])
  · have h := outside (output.toNat + 8 * index, 8 * remaining) (by simp [writes])
    omega

/-- The original right span can alias any other immutable input, but not the
fresh suffix or the lowering slot. -/
theorem narrow_owned {sp output pointer : BitVec 64} {index remaining innerIndex innerRemaining bytes : Nat}
    (low : index ≤ innerIndex) (high : innerIndex + innerRemaining ≤ index + remaining)
    (owned : Protected (writes sp output index remaining) pointer.toNat bytes) :
    Protected (writes sp output innerIndex innerRemaining) pointer.toNat bytes := by
  rcases owned with empty | apart
  · exact Or.inl empty
  · right
    intro span member
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact apart _ (by simp [writes])
    · have h := apart (output.toNat + 8 * index, 8 * remaining) (by simp [writes])
      omega

end SszArm.NatAdd.SmallLoop
