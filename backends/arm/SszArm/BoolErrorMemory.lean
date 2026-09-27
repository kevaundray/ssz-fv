import SszArm.BoolBlockMemory
import SszArm.BoolTails

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

macro "error_reads" : tactic => `(tactic|
  repeat' first
    | rw [write_pair_ones]
    | rw [read_mem_bytes_of_w]
    | rw [read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_same _ 4 _ _ (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 8 4 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | rw [read_mem_bytes_write_mem_bytes_disjoint _ 4 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
    | simp (config := {decide := true, instances := true}) only [state_simp_rules])

/-- Scope-error result fields after actual store blocks and register restoration. -/
theorem scope_tail_result (s : ArmState) (base : BitVec 64) (hs : ScratchSeparated s) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (r (.GPR 0#5) s + BitVec.ofNat 64 offset)
        (returned (afterJump scopeStores s base 4732))).toNat)
      (.error (.scope 1 (r (.GPR 3#5) s).toNat)) := by
  rcases hs with ⟨hsp32, hsp368, hspace, hsep⟩
  simp (config := {decide := true, instances := true})
    [SszNative.BoolCodec.ResultAt, SszNative.BoolCodec.errorAt, SszNative.NatMemory.smallAt,
     afterJump, returned, scopeStores, zeroPair, storeBlock, StoreOp.effect,
     state_simp_rules, BitVec.add_assoc]
  repeat' constructor
  all_goals
    error_reads

/-- Invalid-byte result fields after actual store blocks and register restoration. -/
theorem bad_tail_result (s : ArmState) (base : BitVec 64) (hs : ScratchSeparated s) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (r (.GPR 0#5) s + BitVec.ofNat 64 offset) (badTail s base)).toNat)
      (.error (.notABit (r (.GPR 8#5) s).toNat)) := by
  rcases hs with ⟨hsp32, hsp368, hspace, hsep⟩
  simp (config := {decide := true, instances := true})
    [SszNative.BoolCodec.ResultAt, SszNative.BoolCodec.errorAt, SszNative.NatMemory.smallAt,
     badTail, tagsStored, reasonStored, tagInitialized, afterJump, returned, badStores,
     zeroPair, storeBlock, StoreOp.effect, state_simp_rules, BitVec.add_assoc]
  repeat' constructor
  all_goals
    error_reads

end SszArm.BoolCodec
