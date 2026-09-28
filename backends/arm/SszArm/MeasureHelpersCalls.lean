import SszArm.MeasureContract

namespace SszArm.Measure.Helpers

inductive CallSite where
  | compareCount | constructWidth | propagateError
  deriving DecidableEq

def CallSite.offset : CallSite → Nat
  | .compareCount => 1728
  | .constructWidth => 1912
  | .propagateError => 1940

def CallSite.word : CallSite → BitVec 32
  | .compareCount => 0x97ffd6fc#32
  | .constructWidth => 0x97ffeec1#32
  | .propagateError => 0x94007690#32

def CallSite.target : CallSite → BitVec 64
  | .compareCount => compareOffset
  | .constructWidth => fromU128Offset
  | .propagateError => memcpyOffset

def called (site : CallSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + site.target)
    (w (.GPR 30#5) (base + BitVec.ofNat 64 (site.offset + 4)) s)

theorem call_step (site : CallSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    stepi s = called site s base := by
  change r .PC s = base + BitVec.ofNat 64 site.offset at pc
  have fetched := body_codeAt code (site.offset, site.word) (by
    cases site <;> simp only [CallSite.offset, CallSite.word, bodyProgram, List.mem_append] <;> decide)
  cases site <;> simp only [CallSite.offset, CallSite.word] at pc fetched
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [called, CallSite.offset, CallSite.target, compareOffset, fromU128Offset,
       memcpyOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pc, BitVec.add_assoc]

@[simp] theorem called_program (site : CallSite) (s : ArmState) (base : BitVec 64) :
    (called site s base).program = s.program := by
  simp [called, state_simp_rules]

@[simp] theorem called_error (site : CallSite) (s : ArmState) (base : BitVec 64) :
    read_err (called site s base) = read_err s := by
  simp [called, state_simp_rules]

@[simp] theorem called_pc (site : CallSite) (s : ArmState) (base : BitVec 64) :
    read_pc (called site s base) = base + site.target := by
  simp [called, state_simp_rules]

@[simp] theorem called_link (site : CallSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 30#5) (called site s base) =
      base + BitVec.ofNat 64 (site.offset + 4) := by
  simp [called, state_simp_rules]

@[simp] theorem called_register (site : CallSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notLink : reg ≠ 30#5) :
    r (.GPR reg) (called site s base) = r (.GPR reg) s := by
  simp [called, state_simp_rules, notLink]

@[simp] theorem called_memory (site : CallSite) (s : ArmState) (base : BitVec 64) :
    (called site s base).mem = s.mem := by
  simp [called, state_simp_rules]

@[simp] theorem called_vectors (site : CallSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (called site s base) = r (.SFP reg) s := by
  simp [called, state_simp_rules]

end SszArm.Measure.Helpers
