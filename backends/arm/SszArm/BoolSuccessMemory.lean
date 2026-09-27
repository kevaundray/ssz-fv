import SszArm.BoolBlockMemory
import SszArm.BoolTails

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

macro "success_reads" : tactic => `(tactic|
  repeat' first
    | simp (config := {decide := true, instances := true}) [state_simp_rules, BitVec.add_assoc]
    | rw [read_mem_bytes_of_w]
    | rw [read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_same _ 1 _ _ (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 8 1 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 2 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 1 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_two]
    | simp (config := {decide := true, instances := true}) only [state_simp_rules])

/-- Both success payloads and the result tag survive lowering scratch and RET. -/
theorem success_tail_result (s : ArmState) (base : BitVec 64) (value : Bool)
    (hs : ScratchSeparated s) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (r (.GPR 0#5) s + BitVec.ofNat 64 offset)
        (successTail (if value then trueStores else falseStores) s base)).toNat)
      (.ok (.bool value)) := by
  rcases hs with ⟨hsp32, hsp368, hspace, hsep⟩
  cases value <;>
    simp (config := {decide := true, instances := true})
      [SszNative.BoolCodec.ResultAt, successTail, afterJump, returned, tagStores,
       trueStores, falseStores, storeBlock, StoreOp.effect, state_simp_rules, BitVec.add_assoc]
  all_goals
    constructor <;> success_reads <;> rfl

end SszArm.BoolCodec
