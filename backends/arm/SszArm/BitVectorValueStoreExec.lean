import SszArm.BitVectorValueOps

namespace SszArm.BitVector.ValueTail

open Block

inductive StoreStage where
  | payload | spill | tag | restore
  deriving DecidableEq

def StoreStage.ops : StoreStage → List Op
  | .payload => [p6720, p6724, p6728, p6732]
  | .spill => [p6736, p6740, p6744]
  | .tag => [p6748, p6752, p6756]
  | .restore => [p6760, p6764, p6768, p6772]

def StoreStage.start : StoreStage → Nat
  | .payload => 6720
  | .spill => 6736
  | .tag => 6748
  | .restore => 6760

@[irreducible] def StoreStage.result (stage : StoreStage) (s : ArmState)
    (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  let out := r (.GPR 23#5) s
  match stage with
  | .payload =>
    w .PC (base + 6736#64) (w (.GPR 10#5) 3#64
      (write_mem_bytes 16 (out + 48#64) (r (.GPR 8#5) s ++ r (.GPR 9#5) s)
        (write_mem_bytes 1 (out + 16#64) 3#8
          (write_mem_bytes 16 (out + 32#64) (r (.GPR 20#5) s ++ r (.GPR 24#5) s) s))))
  | .spill =>
    w .PC (base + 6748#64) (w (.GPR 31#5) (sp - 16#64)
      (write_mem_bytes 8 (sp - 8#64) (r (.GPR 10#5) s)
        (write_mem_bytes 8 (sp - 16#64) (r (.GPR 9#5) s) s)))
  | .tag =>
    w .PC (base + 6760#64) (w (.GPR 10#5) 0#64 (w (.GPR 9#5) out
      (write_mem_bytes 8 out 0#64 s)))
  | .restore =>
    w .PC (base + 4732#64) (w (.GPR 31#5) (sp + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 sp s)
        (w (.GPR 10#5) (read_mem_bytes 8 (sp + 8#64) s) s)))

private theorem store_follows (stage : StoreStage) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    Follows base stage.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  cases stage <;>
    simp (config := {decide := true, instances := true})
      [Follows, StoreStage.ops, StoreStage.start, p6720, p6724, p6728, p6732,
       p6736, p6740, p6744, p6748, p6752, p6756, p6760, p6764, p6768, p6772,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       aligned, stack, lower, error, pc, BitVec.add_assoc]

private theorem store_payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6720#64) :
    effect StoreStage.payload.ops s = StoreStage.payload.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, StoreStage.ops, StoreStage.result, p6720, p6724, p6728, p6732,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem store_spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6736#64) :
    effect StoreStage.spill.ops s = StoreStage.spill.result s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, StoreStage.ops, StoreStage.result, p6736, p6740, p6744,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, stack, lower, pc, BitVec.add_assoc, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem zero_move : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide

private theorem store_tag_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6748#64) :
    effect StoreStage.tag.ops s = StoreStage.tag.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, StoreStage.ops, StoreStage.result, p6748, p6752, p6756,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, zero_move] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem store_restore_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6760#64) :
    effect StoreStage.restore.ops s = StoreStage.restore.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, StoreStage.ops, StoreStage.result, p6760, p6764, p6768, p6772,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem store_executes (stage : StoreStage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base := by
  rw [runs stage.ops s base code (store_follows stage s base error aligned pc)]
  cases stage with
  | payload => exact store_payload_summary s base aligned pc
  | spill => exact store_spill_summary s base aligned pc
  | tag => exact store_tag_summary s base aligned pc
  | restore => exact store_restore_summary s base aligned pc

end SszArm.BitVector.ValueTail
