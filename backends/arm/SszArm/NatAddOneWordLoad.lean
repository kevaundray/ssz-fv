import SszArm.NatAddOneWordLoadState
import SszArm.NatAddInputs

namespace SszArm.NatAdd

open UintCodec
open NatCompare (saved read_spill_w)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

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
  exact (block_run base _ s hc he ha
    (one_word_load_follows s base a b hp tag left right)).trans
    (one_word_load_block s base a b tag left right restore)

theorem one_word_load_memory (s : ArmState) (base a b : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame (localWrites s) s (oneWordLoadResult s base a b) := by
  by_cases small : r (.GPR 1#5) s = 0#64
  · have frame := scan_memory (NatCompare.saved_frame s 10#5 stack) stack
    simpa only [Delimited.MemoryFrame, oneWordLoadResult, oneWordSaved, small,
      ↓reduceIte, ArmState.mem_w_eq_mem] using frame
  · intro address outside
    simp [oneWordLoadResult, oneWordSaved, small, state_simp_rules]

end SszArm.NatAdd
