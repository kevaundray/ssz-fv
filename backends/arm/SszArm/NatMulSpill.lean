import SszArm.NatFromU128LowerBase

namespace SszArm.NatMulSpill

open Delimited (Span MemoryFrame)

def six (s : ArmState) (sp a b c d e f : BitVec 64) : ArmState :=
  write_mem_bytes 8 (sp - 8#64) f
    (write_mem_bytes 8 (sp - 16#64) e
      (write_mem_bytes 8 (sp - 24#64) d
        (write_mem_bytes 8 (sp - 32#64) c
          (write_mem_bytes 8 (sp - 40#64) b
            (write_mem_bytes 8 (sp - 48#64) a s)))))

theorem six_reads (s : ArmState) (sp a b c d e f : BitVec 64)
    (stack : 48 ≤ sp.toNat) :
    read_mem_bytes 8 (sp - 48#64) (six s sp a b c d e f) = a ∧
    read_mem_bytes 8 (sp - 40#64) (six s sp a b c d e f) = b ∧
    read_mem_bytes 8 (sp - 32#64) (six s sp a b c d e f) = c ∧
    read_mem_bytes 8 (sp - 24#64) (six s sp a b c d e f) = d ∧
    read_mem_bytes 8 (sp - 16#64) (six s sp a b c d e f) = e ∧
    read_mem_bytes 8 (sp - 8#64) (six s sp a b c d e f) = f := by
  simp (disch := bv_omega) [six, BoolCodec.read_mem_bytes_write_mem_bytes_disjoint,
    BoolCodec.read_mem_bytes_write_mem_bytes_same]

theorem six_frame (s : ArmState) (sp a b c d e f : BitVec 64)
    (stack : 48 ≤ sp.toNat) :
    MemoryFrame [(sp.toNat - 48, 48)] s (six s sp a b c d e f) := by
  intro address outside
  have outsideSpill := outside (sp.toNat - 48, 48) (by simp)
  simp (disch := bv_omega) [six, BoolCodec.write_mem_bytes_frame]

@[simp] theorem six_program (s : ArmState) (sp a b c d e f : BitVec 64) :
    (six s sp a b c d e f).program = s.program := by
  simp [six, state_simp_rules]

@[simp] theorem six_register (s : ArmState) (sp a b c d e f : BitVec 64)
    (reg : BitVec 5) : r (.GPR reg) (six s sp a b c d e f) = r (.GPR reg) s := by
  simp [six, state_simp_rules]

end SszArm.NatMulSpill
