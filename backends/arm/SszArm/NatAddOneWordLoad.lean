import SszArm.NatAddOneWord
import SszArm.NatAddInputs

namespace SszArm.NatAdd

open UintCodec
open NatCompare (saved read_spill_w)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The native low-word fetch chooses its two physical representations without
changing the borrowed arrays. Only the immediate-left route needs a bit-test spill. -/
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

/-- Exact real instruction execution up to the one-word ADD/S. The load premises
are byte observations, not helper correctness or execution assumptions. -/
theorem one_word_load (s : ArmState) (base a b : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 384#64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (tag : r (.GPR 9#5) s = if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64)
    (left : if r (.GPR 1#5) s = 0#64 then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if r (.GPR 3#5) s = 0#64 then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) (oneWordSaved s) = b) :
    run (oneWordLoadOps (r (.GPR 1#5) s) (r (.GPR 3#5) s)).length s =
      oneWordLoadResult s base a b := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s 10#5) =
      r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + 384#64 := hp
  have follows : Follows base (oneWordLoadOps (r (.GPR 1#5) s) (r (.GPR 3#5) s)) s := by
    by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
      by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
      simp_all (config := {decide := true, instances := true})
        [oneWordLoadOps, oneWordSaved, Follows, Op.row, Op.effect, put, next,
          saved, state_simp_rules, read_spill_w, BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [block_run base _ s hc he ha follows]
  simp only [saved] at restore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases r2 : reg = 2#5 <;> by_cases r4 : reg = 4#5 <;>
        by_cases r8 : reg = 8#5 <;> by_cases r10 : reg = 10#5 <;>
        by_cases r31 : reg = 31#5 <;> (try subst reg) <;>
        by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
        by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
        simp_all (config := {decide := true, instances := true})
          [oneWordLoadResult, oneWordLoadOps, oneWordSaved, block, Op.effect, put,
            next, saved, state_simp_rules, read_spill_w, BitVec.add_assoc,
            BitVec.sub_add_cancel]
    | PC =>
      by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
        by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
        simp_all (config := {decide := true, instances := true})
          [oneWordLoadResult, oneWordLoadOps, oneWordSaved, block, Op.effect, put,
            next, saved, state_simp_rules, read_spill_w, BitVec.add_assoc,
            BitVec.sub_add_cancel]
    | SFP reg =>
      by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
        by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
        simp [oneWordLoadResult, oneWordLoadOps, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, saved, state_simp_rules]
    | FLAG flag =>
      by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
        by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
        simp [oneWordLoadResult, oneWordLoadOps, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, saved, state_simp_rules]
    | ERR =>
      by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
        by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
        simp [oneWordLoadResult, oneWordLoadOps, oneWordSaved, smallLeft, smallRight,
          block, Op.effect, put, next, saved, state_simp_rules]
  · by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
      by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordLoadOps, oneWordSaved, smallLeft, smallRight,
        block, Op.effect, put, next, saved, state_simp_rules]
  · intro n address
    by_cases smallLeft : r (.GPR 1#5) s = 0#64 <;>
      by_cases smallRight : r (.GPR 3#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordLoadOps, oneWordSaved, smallLeft, smallRight,
        block, Op.effect, put, next, saved, state_simp_rules, read_spill_w]

theorem one_word_load_memory (s : ArmState) (base a b : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame (localWrites s) s (oneWordLoadResult s base a b) := by
  by_cases small : r (.GPR 1#5) s = 0#64
  · have frame := scan_memory (NatCompare.saved_frame s 10#5 stack) stack
    simpa only [oneWordLoadResult, oneWordSaved, small, ↓reduceIte, ArmState.mem_w_eq_mem] using frame
  · intro address outside
    simp [oneWordLoadResult, oneWordSaved, small, state_simp_rules]

end SszArm.NatAdd
