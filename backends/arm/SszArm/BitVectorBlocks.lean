import SszArm.BitVectorContract
import SszArm.BitVectorProgram

namespace SszArm.BitVector.Block

/-- A literal instruction row with its checked decoder result and image membership.
These are static code facts, not assumptions about an execution state. -/
structure Op where
  offset : Nat
  word : BitVec 32
  instruction : ArmInst
  decoded : decode_raw_inst word = some instruction
  member : (offset, word) ∈ BitVector.program

def Op.checked (offset : Nat) (word : BitVec 32)
    (valid : (decode_raw_inst word).isSome = true)
    (member : (offset, word) ∈ BitVector.program) : Op :=
  { offset, word, instruction := (decode_raw_inst word).get valid, member
    decoded := (Option.some_get valid).symm }

def Op.effect (op : Op) (s : ArmState) : ArmState := exec_inst op.instruction s

theorem Op.step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.offset) : stepi s = op.effect s := by
  exact stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans (code (op.offset, op.word) op.member)) op.decoded

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program :=
  exec_program op.instruction s

def effect (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun state op => op.effect state) s

/-- Internal finite-trace certificate, discharged from each stage's physical
register/memory facts. It is never a premise of the body-entry contract. -/
def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_err s = .None ∧
      read_pc s = base + BitVec.ofNat 64 op.offset ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (follows : Follows base ops s) : run ops.length s = effect ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = effect ops (op.effect s)
    rw [run, op.step s base code follows.1 follows.2.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code) follows.2.2

def p472 : Op := ⟨472, 0xa94927e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 18, Rt2 := 9, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p476 : Op := ⟨476, 0xb940d3fa#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 52, Rn := 31, Rt := 26 }), by rfl, by decide⟩
def p480 : Op := ⟨480, 0xf94053f9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 20, Rn := 31, Rt := 25 }), by rfl, by decide⟩
def p484 : Op := ⟨484, 0xa90427e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 8, Rt2 := 9, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p488 : Op := ⟨488, 0x34005a7a#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 723, Rt := 26 }), by rfl, by decide⟩

def divisionStatus : List Op := [p472, p476, p480, p484, p488]

/-- Whole-state summary: save the exact helper pair and remainder, then branch
on its actual 32-bit status. Unspecified result padding is retained verbatim. -/
@[irreducible] def divisionStatusResult (s : ArmState) (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  let pointer := read_mem_bytes 8 (sp + 144#64) s
  let payload := read_mem_bytes 8 (sp + 152#64) s
  let status := read_mem_bytes 4 (sp + 208#64) s
  let remainder := read_mem_bytes 8 (sp + 160#64) s
  w .PC (if status = 0#32 then base + 3380#64 else base + 492#64)
    (write_mem_bytes 16 (sp + 64#64) (payload ++ pointer)
      (w (.GPR 25#5) remainder (w (.GPR 26#5) (status.setWidth 64)
        (w (.GPR 9#5) payload (w (.GPR 8#5) pointer s)))))

theorem division_status_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 472#64) : run 5 s = divisionStatusResult s base := by
  have follows : Follows base divisionStatus s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    simp (config := {decide := true, instances := true})
      [Follows, divisionStatus, p472, p476, p480, p484, p488, Op.checked, Op.effect,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, error, pc, BitVec.add_assoc]
  have execution := runs divisionStatus s base code follows
  change run 5 s = effect divisionStatus s at execution
  rw [execution]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, divisionStatus, p472, p476, p480, p484, p488, Op.checked, Op.effect,
     exec_inst, divisionStatusResult, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

end SszArm.BitVector.Block
