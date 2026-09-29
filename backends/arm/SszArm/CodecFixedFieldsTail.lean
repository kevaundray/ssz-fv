import SszArm.CodecFixedContextFrame

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)

def fieldTailOps (result : Bool) : List Op :=
  [.p124, .p128, .p132, .p136, .p140, .p144] ++
    if result then [.p160, .p164, .p168] else [.p148, .p152, .p156]

def fieldTail (s : ArmState) (result : Bool) : ArmState := block (fieldTailOps result) s

theorem field_tail_pcs (s : ArmState) (base : BitVec 64) (result : Bool)
    (pc : read_pc s = base + 124#64)
    (returned : r (.GPR 0#5) s = if result then 1#64 else 0#64) :
    PCs base (fieldTailOps result) s := by
  change r .PC s = _ at pc
  cases result <;> simp (config := {decide := true}) [fieldTailOps, PCs, Op.row, Op.effect,
    next, put, branch, state_simp_rules, pc, returned, BitVec.add_assoc]

theorem field_tail_run (s : ArmState) (base : BitVec 64) (result : Bool)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 124#64)
    (returned : r (.GPR 0#5) s = if result then 1#64 else 0#64) :
    run 9 s = fieldTail s result := by
  have executed := run_block (fieldTailOps result) s base code error aligned
    (field_tail_pcs s base result pc returned)
  cases result <;> exact executed

theorem field_tail_pc (s : ArmState) (base : BitVec 64) (result : Bool)
    (pc : read_pc s = base + 124#64)
    (returned : r (.GPR 0#5) s = if result then 1#64 else 0#64) :
    read_pc (fieldTail s result) = base + if result then 108#64 else 172#64 := by
  change r .PC s = _ at pc
  cases result <;> simp (config := {decide := true}) [fieldTail, fieldTailOps, block,
    Op.effect, next, put, branch, state_simp_rules, pc, returned, BitVec.add_assoc,
    BitVec.sub_eq_add_neg]

theorem field_tail_arguments (s : ArmState) (result : Bool) :
    r (.GPR 8#5) (fieldTail s result) = r (.GPR 20#5) s ∧
    r (.GPR 19#5) (fieldTail s result) = r (.GPR 19#5) s - 24#64 ∧
    r (.GPR 31#5) (fieldTail s result) = r (.GPR 31#5) s := by
  cases result <;> simp [fieldTail, fieldTailOps, block, Op.effect, next, put,
    branch, state_simp_rules]

theorem field_tail_memory (s : ArmState) (result : Bool) :
    (fieldTail s result).mem =
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s).mem := by
  cases result <;> simp [fieldTail, fieldTailOps, block, Op.effect, next, put,
    branch, state_simp_rules]
  all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem field_tail_frame (s : ArmState) (result : Bool)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame (Stack.envelope (r (.GPR 31#5) s).toNat 16) s (fieldTail s result) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [Stack.envelope])
  simp only [Prod.fst, Prod.snd] at apart
  rw [field_tail_memory]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)

theorem field_tail_register (s : ArmState) (result : Bool) (reg : BitVec 5)
    (different : reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 19#5 ∧ reg ≠ 31#5) :
    r (.GPR reg) (fieldTail s result) = r (.GPR reg) s := by
  rcases different with ⟨h8, h9, h19, h31⟩
  cases result <;> simp [fieldTail, fieldTailOps, block, Op.effect, next, put,
    branch, state_simp_rules, h8, h9, h19, h31]

theorem BodyContext.field_tail {source current : ArmState} (context : BodyContext source current)
    (enough : 48 ≤ (r (.GPR 31#5) source).toNat) (result : Bool) :
    BodyContext source (fieldTail current result) := by
  have low : 16 ≤ (r (.GPR 31#5) current).toNat := by
    rw [context.saved.sp]
    simp only [bodySP]
    bv_omega
  apply context.lower_frame enough (field_tail_arguments current result).2.2
    (field_tail_frame current result low)
  · intro reg lower upper h19 h20 h30
    exact field_tail_register current result reg ⟨by bv_omega, by bv_omega, h19, by bv_omega⟩
  · intro reg lower upper
    simp only [fieldTail, block_vector]

end SszArm.Codec.Fixed.IsFixed
