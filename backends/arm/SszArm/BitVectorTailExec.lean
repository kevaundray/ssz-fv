import SszArm.BitVectorBlocks
import SszArm.BoolAlignment

namespace SszArm.BitVector.TailCheck

open Block

inductive Stage where
  | prepare | byte | restore | test
  deriving DecidableEq

def p6008 : Op := ⟨6008, 0x8b140308#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 0, shift := 0, Rm := 20, imm6 := 0, Rn := 24, Rd := 8 }), by rfl, by decide⟩
def p6012 : Op := ⟨6012, 0x12000b29#32,
  .DPI (.Logical_imm { sf := 0, opc := 0, N := 0, immr := 0, imms := 2, Rn := 25, Rd := 9 }), by rfl, by decide⟩
def p6016 : Op := ⟨6016, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6020 : Op := ⟨6020, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6024 : Op := ⟨6024, 0x91000109#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 8, Rd := 9 }), by rfl, by decide⟩
def p6028 : Op := ⟨6028, 0xd1000529#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 9, Rd := 9 }), by rfl, by decide⟩
def p6032 : Op := ⟨6032, 0x39400128#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 1, imm12 := 0, Rn := 9, Rt := 8 }), by rfl, by decide⟩
def p6036 : Op := ⟨6036, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6040 : Op := ⟨6040, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6044 : Op := ⟨6044, 0x1ac92508#32,
  .DPR (.Data_processing_two_source { sf := 0, S := 0, Rm := 9, opcode := 9, Rn := 8, Rd := 8 }), by rfl, by decide⟩
def p6048 : Op := ⟨6048, 0x34001088#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 132, Rt := 8 }), by rfl, by decide⟩

def Stage.ops : Stage → List Op
  | .prepare => [p6008, p6012, p6016, p6020]
  | .byte => [p6024, p6028, p6032]
  | .restore => [p6036, p6040]
  | .test => [p6044, p6048]

def Stage.start : Stage → Nat
  | .prepare => 6008
  | .byte => 6024
  | .restore => 6036
  | .test => 6044

@[irreducible] def Stage.result (stage : Stage) (s : ArmState) (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  match stage with
  | .prepare =>
    let count := (((r (.GPR 25#5) s).setWidth 32) &&& 7#32).setWidth 64
    w .PC (base + 6024#64)
      (w (.GPR 31#5) (sp - 16#64) (w (.GPR 9#5) count
        (w (.GPR 8#5) (r (.GPR 24#5) s + r (.GPR 20#5) s)
          (write_mem_bytes 8 (sp - 16#64) count s))))
  | .byte =>
    let address := r (.GPR 8#5) s - 1#64
    w .PC (base + 6036#64) (w (.GPR 8#5) ((read_mem_bytes 1 address s).setWidth 64)
      (w (.GPR 9#5) address s))
  | .restore =>
    w .PC (base + 6044#64) (w (.GPR 31#5) (sp + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 sp s) s))
  | .test =>
    let shifted := (r (.GPR 8#5) s).setWidth 32 >>> (((r (.GPR 9#5) s).setWidth 32).toNat % 32)
    w .PC (if shifted = 0#32 then base + 6576#64 else base + 6052#64)
      (w (.GPR 8#5) (shifted.setWidth 64) s)

private theorem follows (stage : Stage) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) : Follows base stage.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  cases stage <;>
    simp (config := {decide := true, instances := true})
      [Follows, Stage.ops, Stage.start, p6008, p6012, p6016, p6020, p6024, p6028,
       p6032, p6036, p6040, p6044, p6048, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower,
       error, pc, BitVec.add_assoc]

private theorem prepare_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6008#64) :
    effect Stage.prepare.ops s = Stage.prepare.result s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p6008, p6012, p6016, p6020, Op.effect,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, stack, lower,
     pc, BitVec.add_assoc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem byte_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6024#64) :
    effect Stage.byte.ops s = Stage.byte.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p6024, p6028, p6032, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr, store_write_over_write_shadow]

private theorem restore_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6036#64) :
    effect Stage.restore.ops s = Stage.restore.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p6036, p6040, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem shift_count (value : Nat) :
    (((value : Int).bmod 4294967296 % 32) % 64).toNat = value % 32 := by
  rw [Int.bmod_eq_emod]
  split <;> omega

private theorem shift_truncate (word : BitVec 32) (count : Nat) :
    ((word.setWidth 64 >>> count).setWidth 32) = word >>> count := by
  rw [← BitVec.setWidth_ushiftRight (show 32 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]

private theorem test_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6044#64) :
    effect Stage.test.ops s = Stage.test.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p6044, p6048, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, shift_count, shift_truncate,
     aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem executes (stage : Stage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base := by
  rw [runs stage.ops s base code (follows stage s base error aligned pc)]
  cases stage with
  | prepare => exact prepare_summary s base aligned pc
  | byte => exact byte_summary s base aligned pc
  | restore => exact restore_summary s base aligned pc
  | test => exact test_summary s base aligned pc

end SszArm.BitVector.TailCheck
