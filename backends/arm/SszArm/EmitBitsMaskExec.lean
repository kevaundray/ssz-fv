import SszArm.EmitBitsMask
import SszArm.EmitBitsTailOps

namespace SszArm.Emit.Bits

inductive MaskStage where
  | listRemainder | vectorRemainder | listMask | vectorMask | delimiter
  deriving DecidableEq

def MaskStage.start : MaskStage → Nat
  | .listRemainder => 704 | .vectorRemainder => 1312
  | .listMask => 712 | .vectorMask => 1320 | .delimiter => 724

def MaskStage.ops : MaskStage → List Tail.Op
  | .listRemainder => [.p704, .p708] | .vectorRemainder => [.p1312, .p1316]
  | .listMask => [.p712, .p716, .p720] | .vectorMask => [.p1320, .p1324, .p1328]
  | .delimiter => [.p724, .p728, .p732, .p736]

@[irreducible] def maskResult (stage : MaskStage) (s : ArmState) : ArmState := Tail.block stage.ops s

theorem mask_follows (stage : MaskStage) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    Tail.Follows base stage.ops s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  cases stage <;> simp [MaskStage.ops, MaskStage.start, Tail.Follows, Tail.Op.row, Tail.Op.effect,
    Tail.maskRemainder, Activation.put, Activation.next, Dispatch.next,
    state_simp_rules, aligned, CheckSPAlignment, stack, pc, BitVec.add_assoc]

theorem mask_run (stage : MaskStage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = maskResult stage s := by
  rw [maskResult]
  exact Tail.runs _ s base code error (mask_follows stage s base aligned pc)

@[simp] theorem maskResult_program (stage : MaskStage) (s : ArmState) :
    (maskResult stage s).program = s.program := by cases stage <;> simp [maskResult, Tail.block, MaskStage.ops]

@[simp] theorem maskResult_error (stage : MaskStage) (s : ArmState) :
    read_err (maskResult stage s) = read_err s := by cases stage <;> simp [maskResult, Tail.block, MaskStage.ops]

@[simp] theorem maskResult_memory (stage : MaskStage) (s : ArmState) :
    (maskResult stage s).mem = s.mem := by
  cases stage <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect, Tail.maskRemainder,
    Activation.put, Activation.next, Dispatch.next, Dispatch.branch, state_simp_rules]

@[simp] theorem maskResult_register (stage : MaskStage) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 10#5]) : r (.GPR reg) (maskResult stage s) = r (.GPR reg) s := by
  have h8 : reg ≠ 8#5 := by simp_all
  have h9 : reg ≠ 9#5 := by simp_all
  have h10 : reg ≠ 10#5 := by simp_all
  cases stage <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect, Tail.maskRemainder,
    Activation.put, Activation.next, Dispatch.next, Dispatch.branch, state_simp_rules, h8, h9, h10]

@[simp] theorem maskResult_vector (stage : MaskStage) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (maskResult stage s) = r (.SFP reg) s := by
  cases stage <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect, Tail.maskRemainder,
    Activation.put, Activation.next, Dispatch.next, Dispatch.branch, state_simp_rules]

theorem remainder_pc (s : ArmState) (isList : Bool)
    (nonzero : r (.GPR (if isList then 26#5 else 25#5)) s &&& 7#64 ≠ 0#64) :
    read_pc (maskResult (if isList then .listRemainder else .vectorRemainder) s) = read_pc s + 8#64 := by
  cases isList <;> simp_all [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect,
    Tail.maskRemainder, Activation.put, Activation.next, Dispatch.next, Dispatch.branch,
    DPI.update_logical_imm_pstate, zero_flag_spec, state_simp_rules, BitVec.add_assoc]

theorem remainder_word (s : ArmState) (isList : Bool) :
    r (.GPR 9#5) (maskResult (if isList then .listRemainder else .vectorRemainder) s) =
      r (.GPR (if isList then 26#5 else 25#5)) s &&& 7#64 := by
  cases isList <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect,
    Tail.maskRemainder, Activation.put, Activation.next, Dispatch.next, Dispatch.branch, state_simp_rules]

theorem remainder_byte (s : ArmState) (isList : Bool) :
    r (.GPR 8#5) (maskResult (if isList then .listRemainder else .vectorRemainder) s) = r (.GPR 8#5) s := by
  cases isList <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect,
    Tail.maskRemainder, Activation.put, Activation.next, Dispatch.next, Dispatch.branch, state_simp_rules]

theorem masked_pc (s : ArmState) (isList : Bool) :
    read_pc (maskResult (if isList then .listMask else .vectorMask) s) = read_pc s + 12#64 := by
  cases isList <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect,
    Activation.put, Activation.next, state_simp_rules, BitVec.add_assoc]

theorem masked_byte (s : ArmState) (isList : Bool) (small : (r (.GPR 9#5) s).toNat < 8) :
    (r (.GPR 8#5) (maskResult (if isList then .listMask else .vectorMask) s)).setWidth 8 =
      maskByte ((r (.GPR 8#5) s).setWidth 8) (r (.GPR 9#5) s).toNat := by
  have narrow : ((r (.GPR 9#5) s).setWidth 32).toNat = (r (.GPR 9#5) s).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have modulo : (r (.GPR 9#5) s).toNat % 32 = (r (.GPR 9#5) s).toNat := Nat.mod_eq_of_lt (by omega)
  cases isList <;> simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect, Tail.shift32,
    Activation.put, Activation.next, state_simp_rules, narrow, modulo, maskByte,
    BitVec.setWidth_and, BitVec.setWidth_not]

theorem delimiter_pc (s : ArmState) : read_pc (maskResult .delimiter s) = read_pc s + 764#64 := by
  simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect, Activation.put, Activation.next,
    state_simp_rules, BitVec.add_assoc]

theorem delimiter_byte (s : ArmState) (small : (r (.GPR 25#5) s).toNat < 8) :
    (r (.GPR 8#5) (maskResult .delimiter s)).setWidth 8 =
      ((r (.GPR 8#5) s).setWidth 8) ||| (1#8 <<< (r (.GPR 25#5) s).toNat) := by
  have narrow : ((r (.GPR 25#5) s).setWidth 32).toNat = (r (.GPR 25#5) s).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have modulo : (r (.GPR 25#5) s).toNat % 32 = (r (.GPR 25#5) s).toNat := Nat.mod_eq_of_lt (by omega)
  simp [maskResult, Tail.block, MaskStage.ops, Tail.Op.effect, Tail.shift32,
    Activation.put, Activation.next, state_simp_rules, narrow, modulo, BitVec.setWidth_or]

end SszArm.Emit.Bits
