import SszArm.NatDivisionPhysical

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- After the prologue only the bottom lowering slot is writable. Keeping the
saved 64-byte activation out of this footprint makes LR restoration compositional. -/
def bodyWrites (original : ArmState) (operand : SszNative.NatOperand) : List Span :=
  let local := [((r (.GPR 0#5) original).toNat, 68),
    ((r (.GPR 31#5) original).toNat - 80, 16)]
  match (outcome original operand).allocation with
  | none => local
  | some reservation => local ++ [((r (.GPR 4#5) original).toNat + 16, 8),
      (reservation.pointer, 8 * (outcome original operand).written.length)]

/-- Embedding a tight physical frame in larger allowed intervals. -/
theorem frame_cover {small large : List Span} {s t : ArmState}
    (frame : MemoryFrame small s t)
    (cover : ∀ span ∈ small, ∃ enclosing ∈ large,
      enclosing.1 ≤ span.1 ∧ span.1 + span.2 ≤ enclosing.1 + enclosing.2) :
    MemoryFrame large s t := by
  intro a outside
  apply frame a
  intro span member
  obtain ⟨enclosing, present, low, high⟩ := cover span member
  have apart := outside enclosing present
  omega

theorem body_frame_full {original s t : ArmState} (operand : SszNative.NatOperand)
    (frame : MemoryFrame (bodyWrites original operand) s t) :
    MemoryFrame (writesFor original (outcome original operand)) s t := by
  apply frame_cover frame
  intro span member
  cases allocated : (outcome original operand).allocation with
  | none =>
    simp only [bodyWrites, allocated, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ⟨_, by simp [writesFor, allocated, localWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨((r (.GPR 31#5) original).toNat - 80, 80),
        by simp [writesFor, allocated, localWrites], Nat.le_refl _, by omega⟩
  | some reservation =>
    simp only [bodyWrites, allocated, List.mem_append, List.mem_cons, List.mem_singleton] at member
    rcases member with (rfl | rfl) | (rfl | rfl)
    · exact ⟨_, by simp [writesFor, allocated, localWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨((r (.GPR 31#5) original).toNat - 80, 80),
        by simp [writesFor, allocated, localWrites], Nat.le_refl _, by omega⟩
    · exact ⟨_, by simp [writesFor, allocated], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [writesFor, allocated], Nat.le_refl _, Nat.le_refl _⟩

theorem Owned.body_activation {original : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) :
    Protected (bodyWrites original operand) ((r (.GPR 31#5) original).toNat - 64) 64 := by
  have stack := owned.stackBound
  have out : (r (.GPR 0#5) original).toNat + 68 ≤ (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ (r (.GPR 0#5) original).toNat := by
    rcases owned.outputStack with empty | apart
    · omega
    · have h := apart ((r (.GPR 31#5) original).toNat - 80, 80) (by simp)
      simp only [Prod.fst, Prod.snd] at h
      omega
  have arena : (r (.GPR 4#5) original).toNat + 24 ≤ (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ (r (.GPR 4#5) original).toNat := by
    rcases owned.arenaLocal with empty | apart
    · omega
    · have h := apart ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at h
      omega
  right
  intro span member
  cases allocated : (outcome original operand).allocation with
  | none =>
    simp only [bodyWrites, allocated, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega
  | some reservation =>
    have fresh := owned.fresh reservation allocated
    have positive : 0 < (outcome original operand).written.length := by
      have resources := SszNative.NatDivision.allocation_resources operand (r (.GPR 3#5) original)
        (arenaOf original).base (arenaOf original).capacity (arenaOf original).used reservation allocated
      have length := resources.2.1
      change (outcome original operand).written.length = _ at length
      split at length <;> omega
    have payload : reservation.pointer + 8 * (outcome original operand).written.length ≤
        (r (.GPR 31#5) original).toNat - 80 ∨
        (r (.GPR 31#5) original).toNat ≤ reservation.pointer := by
      rcases fresh with empty | apart
      · omega
      · have h := apart ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
        simp only [Prod.fst, Prod.snd] at h
        omega
    simp only [bodyWrites, allocated, List.mem_append, List.mem_cons, List.mem_singleton] at member
    rcases member with (rfl | rfl) | (rfl | rfl) <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem Saved.body_preserved {original s t : ArmState} {operand : SszNative.NatOperand}
    (saved : Saved original s) (owned : Owned original operand)
    (frame : MemoryFrame (bodyWrites original operand) s t)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (high : ∀ reg : BitVec 5, 25 ≤ reg.toNat → reg.toNat ≤ 29 →
      r (.GPR reg) t = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) : Saved original t :=
  saved.preserve owned.stackBound frame owned.body_activation sp high vectors

end SszArm.NatDivision
