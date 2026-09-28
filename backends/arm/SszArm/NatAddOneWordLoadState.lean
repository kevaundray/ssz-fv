import SszArm.NatAddOneWord
import SszArm.NatAddLoopMemory

namespace SszArm.NatAdd

open UintCodec
open NatCompare (saved read_spill_w)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The actual representation-selecting fetch, including the immediate-left spill. -/
def oneWordLoadOps (left right : BitVec 64) : List Op :=
  [.p384] ++ (if left = 0#64 then
    [.p880, .p884, .p888, .p892, .p896] ++
      (if right = 0#64 then [.p900, .p904, .p908, .p924] else [.p912, .p916, .p920])
  else [.p388, .p392, .p396, .p400] ++ (if right = 0#64 then [.p404] else [])) ++
  (if right = 0#64 then [] else [.p972, .p976])

def oneWordSaved (s : ArmState) : ArmState :=
  if r (.GPR 1#5) s = 0#64 then saved s 10#5 else s

def oneWordLoadResult (s : ArmState) (base a b : BitVec 64) : ArmState :=
  w .PC (base + 980#64) (w (.GPR 4#5) b (w (.GPR 2#5) a
    (w (.GPR 8#5) 0#64 (oneWordSaved s))))

theorem one_word_zero_payload (s : ArmState) (a : BitVec 64) :
    w (.GPR 8#5) 0#64 (w (.GPR 2#5) a s) =
      w (.GPR 2#5) a (w (.GPR 8#5) 0#64 s) :=
  w_of_w_commute (by decide)

/-- Control observations only: neither execution nor the code image enters this
bounded simplification of the four real representation paths. -/
theorem one_word_load_follows (s : ArmState) (base a b : BitVec 64)
    (hp : r .PC s = base + 384#64)
    (tag : r (.GPR 9#5) s = if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64)
    (left : if r (.GPR 1#5) s = 0#64 then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if r (.GPR 3#5) s = 0#64 then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) (oneWordSaved s) = b) :
    Follows base (oneWordLoadOps (r (.GPR 1#5) s) (r (.GPR 3#5) s)) s := by
  by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
    by_cases smallRight : r (.GPR 3#5) s = 0#64
  all_goals
    simp only [oneWordSaved, smallLeft, smallRight, ↓reduceIte] at left right tag
    simp (config := {decide := true})
      [oneWordLoadOps, smallLeft, smallRight, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, read_spill_w, hp, tag, left, right,
        BitVec.add_assoc, BitVec.sub_add_cancel]

/-- Exact state algebra reuses the opaque temporary-restoration contract. It
never expands the byte store or multiplies instruction cases by state fields. -/
theorem one_word_load_block (s : ArmState) (base a b : BitVec 64)
    (tag : r (.GPR 9#5) s = if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64)
    (left : if r (.GPR 1#5) s = 0#64 then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if r (.GPR 3#5) s = 0#64 then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) (oneWordSaved s) = b)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s 10#5) =
      r (.GPR 10#5) s) :
    block base (oneWordLoadOps (r (.GPR 1#5) s) (r (.GPR 3#5) s)) s =
      oneWordLoadResult s base a b := by
  simp only [saved] at restore
  by_cases smallLeft : r (.GPR 1#5) s = 0#64
  · simp only [smallLeft, ↓reduceIte] at left
    have restored := store_restore_fields (w (.GPR 8#5) 0#64 (saved s 10#5)) 10#5
      ((((r (.GPR 9#5) s).setWidth 32) &&& 1#32).setWidth 64) (by decide)
    have keep2 : w (.GPR 2#5) a (w (.GPR 8#5) 0#64 (saved s 10#5)) =
        w (.GPR 8#5) 0#64 (saved s 10#5) := by
      have value : r (.GPR 2#5) (w (.GPR 8#5) 0#64 (saved s 10#5)) = a := by
        simpa [saved, state_simp_rules] using left
      rw [←value, w_irrelevant]
    simp only [saved, state_simp_rules] at restored
    simp only [saved] at keep2
    by_cases smallRight : r (.GPR 3#5) s = 0#64
    · simp only [smallRight, ↓reduceIte] at right tag
      have keep4 : w (.GPR 4#5) b (w (.GPR 8#5) 0#64 (saved s 10#5)) =
          w (.GPR 8#5) 0#64 (saved s 10#5) := by
        have value : r (.GPR 4#5) (w (.GPR 8#5) 0#64 (saved s 10#5)) = b := by
          simpa [saved, state_simp_rules] using right
        rw [←value, w_irrelevant]
      simp only [saved] at keep4
      simpa (config := {decide := true})
        [oneWordLoadOps, oneWordLoadResult, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, saved, load_store_field, load_gpr_pc,
          state_simp_rules, read_spill_w, BitVec.add_assoc, BitVec.sub_add_cancel,
          restore, tag, keep2, keep4] using
        congrArg (w .PC (base + 980#64)) restored
    · simp only [oneWordSaved, smallLeft, smallRight, ↓reduceIte, saved] at right tag
      simpa (config := {decide := true})
        [oneWordLoadOps, oneWordLoadResult, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, saved, load_store_field, load_gpr_pc,
          state_simp_rules, read_spill_w, BitVec.add_assoc, BitVec.sub_add_cancel,
          restore, right, tag, keep2] using
        congrArg (fun t => w .PC (base + 980#64) (w (.GPR 4#5) b t)) restored
  · simp only [smallLeft, ↓reduceIte] at left
    by_cases smallRight : r (.GPR 3#5) s = 0#64
    · simp only [smallRight, ↓reduceIte] at right tag
      have keep4 : w (.GPR 4#5) b (w (.GPR 2#5) a (w (.GPR 8#5) 0#64 s)) =
          w (.GPR 2#5) a (w (.GPR 8#5) 0#64 s) := by
        have value : r (.GPR 4#5) (w (.GPR 2#5) a (w (.GPR 8#5) 0#64 s)) = b := by
          simpa [state_simp_rules] using right
        rw [←value, w_irrelevant]
      simp (config := {decide := true})
        [oneWordLoadOps, oneWordLoadResult, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, state_simp_rules,
          load_gpr_pc, one_word_zero_payload, BitVec.add_assoc,
          left, tag, keep4]
    · simp only [oneWordSaved, smallLeft, smallRight, ↓reduceIte] at right tag
      simp (config := {decide := true})
        [oneWordLoadOps, oneWordLoadResult, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, state_simp_rules,
          load_gpr_pc, one_word_zero_payload, BitVec.add_assoc, left, right, tag]

end SszArm.NatAdd
