import SszArm.BitVectorMemory

namespace SszArm.Codec.Stack

open Delimited (Span Protected MemoryFrame)
open BitVector (Covers)

/-- A caller-owned descending stack interval. The size is supplied by the
function's recursive call bound; this definition imposes no bound on recursion. -/
def envelope (sp bytes : Nat) : List Span := [(sp - bytes, bytes)]

@[simp] theorem envelope_end {sp bytes : Nat} (enough : bytes ≤ sp) :
    sp - bytes + bytes = sp := Nat.sub_add_cancel enough

/-- A child activation begins below the caller's actual frame, not below the
original entry SP. Helper/lowering requirements belong to `child`. -/
theorem child_low {sp frame child total : Nat}
    (enough : total ≤ sp) (within : frame + child ≤ total) :
    child ≤ sp - frame := by omega

theorem caller_low {sp frame child total : Nat}
    (enough : total ≤ sp) (within : frame + child ≤ total) : frame ≤ sp := by omega

theorem child_cover {sp frame child total : Nat}
    (enough : total ≤ sp) (within : frame + child ≤ total) :
    Covers (envelope sp total) (envelope (sp - frame) child) := by
  intro span member
  simp only [envelope, List.mem_singleton] at member
  subst span
  refine ⟨(sp - total, total), by simp [envelope], ?_, ?_⟩ <;> dsimp <;> omega

theorem caller_cover {sp frame total : Nat}
    (enough : total ≤ sp) (within : frame ≤ total) :
    Covers (envelope sp total) (envelope sp frame) := by
  intro span member
  simp only [envelope, List.mem_singleton] at member
  subst span
  refine ⟨(sp - total, total), by simp [envelope], ?_, ?_⟩ <;> dsimp <;> omega

/-- An individual live slot may be framed without claiming that the whole
reserved stack envelope was initialized. -/
theorem slot_cover {sp total displacement bytes : Nat}
    (enough : total ≤ sp) (low : bytes ≤ displacement) (high : displacement ≤ total) :
    Covers (envelope sp total) [(sp - displacement, bytes)] := by
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  refine ⟨(sp - total, total), by simp [envelope], ?_, ?_⟩ <;> dsimp <;> omega

theorem child_protected {sp frame child total address bytes : Nat}
    (enough : total ≤ sp) (within : frame + child ≤ total)
    (owned : Protected (envelope sp total) address bytes) :
    Protected (envelope (sp - frame) child) address bytes :=
  (child_cover enough within).protected owned

theorem caller_protected {sp frame total address bytes : Nat}
    (enough : total ≤ sp) (within : frame ≤ total)
    (owned : Protected (envelope sp total) address bytes) :
    Protected (envelope sp frame) address bytes :=
  (caller_cover enough within).protected owned

/-- A callee's descending stack cannot overwrite a caller slot above its entry
SP, including a partially initialized result area. -/
theorem caller_slot_protected {sp frame child displacement bytes : Nat}
    (enough : frame + child ≤ sp) (inside : displacement + bytes ≤ frame) :
    Protected (envelope (sp - frame) child) (sp - frame + displacement) bytes := by
  right
  intro span member
  simp only [envelope, List.mem_singleton] at member
  subst span
  right
  dsimp
  omega

theorem child_frame {sp frame child total : Nat} {s t : ArmState}
    (enough : total ≤ sp) (within : frame + child ≤ total)
    (framed : MemoryFrame (envelope (sp - frame) child) s t) :
    MemoryFrame (envelope sp total) s t :=
  (child_cover enough within).frame framed

/-- Numeric SP descent agrees with the actual 64-bit SUB when the original
physical stack envelope fits. -/
theorem sub_toNat (sp : BitVec 64) (frame : Nat) (enough : frame ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 frame).toNat = sp.toNat - frame := by
  bv_omega

/-- Stack reservations from different calls are composed by maximum, not by
summing sibling activations that never coexist. -/
theorem max_child_left {sp frame left right : Nat}
    (enough : frame + max left right ≤ sp) : frame + left ≤ sp := by
  have bounded := Nat.le_max_left left right
  omega

theorem max_child_right {sp frame left right : Nat}
    (enough : frame + max left right ≤ sp) : frame + right ≤ sp := by
  have bounded := Nat.le_max_right left right
  omega

end SszArm.Codec.Stack
