import SszArm.IndicesGeneralizedIndexEmptyGeometry
import SszArm.UintResultMemory

namespace SszArm.Indices.GeneralizedIndex.Empty

open Dispatch.Block (next put save branch)
open Delimited (Span MemoryFrame)

/-- Exact store order on the real empty path. The two lowering saves are kept
separate, even though both save the same original temporary values. -/
def emptyMemory (s : ArmState) : ArmState :=
  let m := write_mem_bytes 8 (stackSlot s 80) (r (.GPR 30#5) s) s
  let m := write_mem_bytes 16 (stackSlot s 64) (r (.GPR 25#5) s ++ r (.GPR 26#5) s) m
  let m := write_mem_bytes 16 (stackSlot s 48) (r (.GPR 23#5) s ++ r (.GPR 24#5) s) m
  let m := write_mem_bytes 16 (stackSlot s 32) (r (.GPR 21#5) s ++ r (.GPR 22#5) s) m
  let m := write_mem_bytes 16 (stackSlot s 16) (r (.GPR 19#5) s ++ r (.GPR 20#5) s) m
  let m := write_mem_bytes 8 (stackSlot s 240) (r (.GPR 9#5) s) m
  let m := write_mem_bytes 8 (stackSlot s 232) (r (.GPR 10#5) s) m
  let m := write_mem_bytes 8 (r (.GPR 0#5) s) 0#64 m
  let m := write_mem_bytes 8 (r (.GPR 0#5) s + 8#64) 1#64 m
  let m := write_mem_bytes 8 (stackSlot s 240) (r (.GPR 9#5) s) m
  let m := write_mem_bytes 8 (stackSlot s 232) (r (.GPR 10#5) s) m
  write_mem_bytes 4 (r (.GPR 0#5) s + 64#64) 0#32 m

/-- Only the actual saved slots, lowering slot, Nat header, and reason are writable. -/
def emptyWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 80, 8),
   ((r (.GPR 31#5) s).toNat - 64, 64),
   ((r (.GPR 31#5) s).toNat - 240, 16),
   ((r (.GPR 0#5) s).toNat, 16),
   ((r (.GPR 0#5) s).toNat + 64, 4)]

theorem emptyMemory_frame (s : ArmState) (owned : Owned s) :
    MemoryFrame (emptyWrites s) s (emptyMemory s) := by
  intro address outside
  have savedLR := outside ((r (.GPR 31#5) s).toNat - 80, 8) (by simp [emptyWrites])
  have savedRegs := outside ((r (.GPR 31#5) s).toNat - 64, 64) (by simp [emptyWrites])
  have lowering := outside ((r (.GPR 31#5) s).toNat - 240, 16) (by simp [emptyWrites])
  have result := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [emptyWrites])
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [emptyWrites])
  have spBound := (r (.GPR 31#5) s).isLt
  have low := owned.stackLow
  have resultBound := owned.outputBound
  have p8 := output_toNat s owned 8 (by decide)
  have p64 := output_toNat s owned 64 (by decide)
  dsimp at savedLR savedRegs lowering result status
  simp only [emptyMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ _ _ address
    (by first | (rw [stackSlot_toNat s owned _ (by decide)]; omega) | (rw [p8]; omega) |
      (rw [p64]; omega) | omega)
    (by first | (rw [stackSlot_toNat s owned _ (by decide)]; omega) | (rw [p8]; omega) |
      (rw [p64]; omega) | omega)]

end SszArm.Indices.GeneralizedIndex.Empty
