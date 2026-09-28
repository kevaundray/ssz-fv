import SszArm.BitVectorValueOps

namespace SszArm.BitVector.ValueTail

open Block

def shift3 (word : BitVec 64) : BitVec 64 :=
  BitVec.ror word 3 &&& 2305843009213693951#64

inductive LoadStage where
  | tag | someRestore | payload | shift | shiftRestore
  deriving DecidableEq

def LoadStage.ops : LoadStage → List Op
  | .tag => [p6592, p6596, p6600, p6604, p6608]
  | .someRestore => [p6612, p6616, p6620]
  | .payload => [p6636, p6640, p6644]
  | .shift => [p6648, p6652]
  | .shiftRestore => [p6656, p6660]

def LoadStage.start : LoadStage → Nat
  | .tag => 6592
  | .someRestore => 6612
  | .payload => 6636
  | .shift => 6648
  | .shiftRestore => 6656

@[irreducible] def LoadStage.result (stage : LoadStage) (s : ArmState)
    (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  match stage with
  | .tag =>
    let tag := read_mem_bytes 4 (sp + 144#64) s
    let bit := tag &&& 1#32
    w .PC (if bit = 0#32 then base + 6624#64 else base + 6612#64)
      (w (.GPR 9#5) (bit.setWidth 64) (w (.GPR 31#5) (sp - 16#64)
        (w (.GPR 8#5) (tag.setWidth 64)
          (write_mem_bytes 8 (sp - 16#64) (r (.GPR 9#5) s) s))))
  | .someRestore =>
    w .PC (base + 6636#64) (w (.GPR 31#5) (sp + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 sp s) s))
  | .payload =>
    w .PC (base + 6648#64)
      (w (.GPR 31#5) (sp - 16#64)
        (w (.GPR 8#5) (read_mem_bytes 8 (sp + 168#64) s)
          (w (.GPR 9#5) (read_mem_bytes 8 (sp + 160#64) s)
            (write_mem_bytes 8 (sp - 16#64) (r (.GPR 11#5) s) s))))
  | .shift =>
    let low := shift3 (r (.GPR 9#5) s)
    w .PC (base + 6656#64)
      (w (.GPR 10#5) (low ||| (r (.GPR 8#5) s <<< (61 : Nat)))
        (w (.GPR 11#5) low s))
  | .shiftRestore =>
    w .PC (base + 6664#64) (w (.GPR 31#5) (sp + 16#64)
      (w (.GPR 11#5) (read_mem_bytes 8 sp s) s))

private theorem load_follows (stage : LoadStage) (s : ArmState) (base : BitVec 64)
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
      [Follows, LoadStage.ops, LoadStage.start, p6592, p6596, p6600, p6604, p6608,
       p6612, p6616, p6620, p6636, p6640, p6644, p6648, p6652, p6656, p6660,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, stack, lower,
       error, pc, BitVec.add_assoc]

private theorem tag_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6592#64) :
    effect LoadStage.tag.ops s = LoadStage.tag.result s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [effect, LoadStage.ops, LoadStage.result, p6592, p6596, p6600, p6604, p6608,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, stack, lower, pc, BitVec.add_assoc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem some_restore_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6612#64) :
    effect LoadStage.someRestore.ops s = LoadStage.someRestore.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, LoadStage.ops, LoadStage.result, p6612, p6616, p6620,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6636#64) :
    effect LoadStage.payload.ops s = LoadStage.payload.result s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [effect, LoadStage.ops, LoadStage.result, p6636, p6640, p6644,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     aligned, stack, lower, pc, BitVec.add_assoc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

theorem and_ones (word : BitVec 64) : word &&& 18446744073709551615#64 = word :=
  BitVec.and_allOnes

private theorem shift_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6648#64) :
    effect LoadStage.shift.ops s = LoadStage.shift.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, LoadStage.ops, LoadStage.result, shift3, p6648, p6652,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, and_ones] <;>
    simp only [w, write_base_pc, write_base_gpr, store_write_over_write_shadow]

private theorem shift_restore_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6656#64) :
    effect LoadStage.shiftRestore.ops s = LoadStage.shiftRestore.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, LoadStage.ops, LoadStage.result, p6656, p6660,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem load_executes (stage : LoadStage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base := by
  rw [runs stage.ops s base code (load_follows stage s base error aligned pc)]
  cases stage with
  | tag => exact tag_summary s base aligned pc
  | someRestore => exact some_restore_summary s base aligned pc
  | payload => exact payload_summary s base aligned pc
  | shift => exact shift_summary s base pc
  | shiftRestore => exact shift_restore_summary s base aligned pc

end SszArm.BitVector.ValueTail
