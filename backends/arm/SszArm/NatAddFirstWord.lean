import SszArm.NatAddOneWord
import SszArm.NatAddFirstWordState
import SszArm.NatAddContract

namespace SszArm.NatAdd

open UintCodec
open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The first word is stored before either general carry loop is entered. -/
structure FirstWordPost (kind : FirstKind) (s t : ArmState) (base a b : BitVec 64) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [11#5, 12#5, 13#5, 14#5, 15#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  first : r (.GPR 11#5) t = a + b
  carry : r (.GPR 12#5) t = if 2^64 ≤ a.toNat + b.toNat then 1#64 else 0#64
  flag : kind ≠ .smallLarge → r (.GPR 13#5) t = if kind = .largeSmall then 1#64 else 0#64
  remaining : kind ≠ .smallLarge → r (.GPR 14#5) t = r (.GPR 8#5) s
  index : kind ≠ .smallLarge → r (.GPR 15#5) t = 1#64
  pc : read_pc t = base + (if kind = .smallLarge then 1868#64 else 1692#64)
  stored : read_mem_bytes 8 (r (.GPR 9#5) s) t = a + b
  memory : MemoryFrame [((r (.GPR 9#5) s).toNat, 8)] s t

/-- All physically reachable first-word paths for the multiword branch. The
remaining Small/Small machine branch is excluded by the proven width classifier. -/
theorem first_word_run (s : ArmState) (base a b : BitVec 64) (kind : FirstKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 276#64)
    (physical : (r (.GPR 9#5) s).toNat + 8 ≤ 2^64)
    (leftKind : r (.GPR 1#5) s = 0#64 ↔ kind = .smallLarge)
    (rightKind : r (.GPR 3#5) s = 0#64 ↔ kind = .largeSmall)
    (left : if kind = .smallLarge then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if kind = .largeSmall then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) s = b) :
    let ops := kind.ops (sumOverflow a b)
    let t := block base ops s
    run ops.length s = t ∧ FirstWordPost kind s t base a b := by
  have memory := first_word_memory s base a b kind left right
  obtain ⟨first, carry, flag, remaining, index, pc⟩ :=
    first_word_fields s base a b kind leftKind left right
  refine ⟨block_run base _ s hc he ha
    (first_word_follows s base a b kind hp leftKind rightKind left right),
    ⟨block_program _ _ _, block_error _ _ _,
      first_word_registers s base kind _, first_word_vectors s base kind _,
      first, carry, flag, remaining, index, pc, ?_, ?_⟩⟩
  · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) 8 (r (.GPR 9#5) s)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ physical
  · intro address outside
    rw [memory]
    exact (Delimited.store_frame s _ 8 _ physical) address outside

end SszArm.NatAdd
