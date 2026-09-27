import SszArm.NatDivisionImpl
import SszArm.Udivti3Proofs
import SszLimbDivision

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The five real BL instructions in the linked private helper. -/
inductive CallSite where
  | small | wide | limb | low | zero
  deriving DecidableEq

def CallSite.offset : CallSite → Nat
  | .small => 316
  | .wide => 360
  | .limb => 564
  | .low => 636
  | .zero => 676

def CallSite.word : CallSite → BitVec 32
  | .small => 0x9400b213#32
  | .wide => 0x9400b208#32
  | .limb => 0x9400b1d5#32
  | .low => 0x9400b1c3#32
  | .zero => 0x9400b1b9#32

/-- Instruction-memory obligations only; the division semantics come from the
proved runtime callee rather than a hypothesis about a helper's behavior. -/
def JointCodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  CodeAt s base ∧ Udivti3.CodeAt s (base + BitVec.ofNat 64 udivOffset)

def called (site : CallSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 udivOffset)
    (w (.GPR 30#5) (base + BitVec.ofNat 64 (site.offset + 4)) s)

theorem call_step (site : CallSite) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (hp : read_pc s = base + BitVec.ofNat 64 site.offset) :
    stepi s = called site s base := by
  have hf := hc (site.offset, site.word) (by cases site <;> decide)
  cases site <;> simp only [CallSite.offset, CallSite.word] at hp hf ⊢
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    have hpc : r .PC s = _ := hp
    simp (config := {decide := true, instances := true})
      [exec_inst, called, CallSite.offset, udivOffset, state_simp_rules,
       bitvec_rules, minimal_theory, hpc, BitVec.add_assoc]

def callResult (site : CallSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  Udivti3.result (called site s base)

def callFuel (site : CallSite) (s : ArmState) (base : BitVec 64) : Nat :=
  Udivti3.fuel (called site s base) + 1

/-- Executes the BL, every runtime division instruction, and its actual RET. -/
theorem call_run (site : CallSite) (s : ArmState) (base : BitVec 64)
    (hc : JointCodeAt s base) (he : read_err s = .None)
    (hp : read_pc s = base + BitVec.ofNat 64 site.offset)
    (hd : 0 < Udivti3.divisor s) :
    run (callFuel site s base) s = callResult site s base := by
  have cq : Udivti3.CodeAt (called site s base) (base + BitVec.ofNat 64 udivOffset) := by
    simpa [Udivti3.CodeAt, SszArm.CodeAt, called, state_simp_rules] using hc.2
  have eq : read_err (called site s base) = .None := by
    simpa [called, state_simp_rules] using he
  have pq : read_pc (called site s base) = base + BitVec.ofNat 64 udivOffset := by
    simp [called, state_simp_rules]
  have dq : 0 < Udivti3.divisor (called site s base) := by
    simpa [Udivti3.divisor, called, state_simp_rules] using hd
  rw [callFuel, run, call_step site s base hc.1 he hp]
  exact Udivti3.program_run _ _ cq pq eq dq

@[simp] theorem call_memory (site : CallSite) (s : ArmState) (base : BitVec 64) :
    (callResult site s base).mem = s.mem := by
  rw [callResult, Udivti3.result_memory]
  simp [called, state_simp_rules]

@[simp] theorem call_program (site : CallSite) (s : ArmState) (base : BitVec 64) :
    (callResult site s base).program = s.program := by
  rw [callResult, Udivti3.result_program]
  simp [called, state_simp_rules]

theorem call_frame (site : CallSite) (s : ArmState) (base : BitVec 64)
    (f : StateField) (hf : Udivti3.Preserved f) :
    r f (callResult site s base) = r f (called site s base) :=
  Udivti3.result_frame _ f hf

@[simp] theorem call_err (site : CallSite) (s : ArmState) (base : BitVec 64) :
    read_err (callResult site s base) = read_err s := by
  have h := call_frame site s base .ERR trivial
  simpa [called, state_simp_rules] using h

@[simp] theorem call_sp (site : CallSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (callResult site s base) = r (.GPR 31#5) s := by
  have h := call_frame site s base (.GPR 31#5) (by decide)
  simpa [called, state_simp_rules] using h

@[simp] theorem call_sfp (site : CallSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (callResult site s base) = r (.SFP reg) s := by
  have h := call_frame site s base (.SFP reg) trivial
  simpa [called, state_simp_rules] using h

theorem call_gpr (site : CallSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (lo : 9 ≤ reg.toNat) (hi : reg.toNat ≤ 29) :
    r (.GPR reg) (callResult site s base) = r (.GPR reg) s := by
  have preserved : Udivti3.Preserved (.GPR reg) := by
    simp only [Udivti3.Preserved]
    bv_omega
  have notLink : reg ≠ 30#5 := by bv_omega
  have h := call_frame site s base (.GPR reg) preserved
  simpa [called, state_simp_rules, notLink] using h

theorem call_return (site : CallSite) (s : ArmState) (base : BitVec 64)
    (hd : 0 < Udivti3.divisor s) :
    read_pc (callResult site s base) = base + BitVec.ofNat 64 (site.offset + 4) := by
  have pq : read_pc (called site s base) = base + BitVec.ofNat 64 udivOffset := by
    simp [called, state_simp_rules]
  have dq : 0 < Udivti3.divisor (called site s base) := by
    simpa [Udivti3.divisor, called, state_simp_rules] using hd
  have h := Udivti3.result_return (called site s base) _ pq dq
  simpa [callResult, called, state_simp_rules] using h

theorem call_quotient (site : CallSite) (s : ArmState) (base : BitVec 64)
    (hd : 0 < Udivti3.divisor s) :
    Udivti3.numerator (callResult site s base) =
      Udivti3.numerator s / Udivti3.divisor s := by
  have pq : read_pc (called site s base) = base + BitVec.ofNat 64 udivOffset := by
    simp [called, state_simp_rules]
  have dq : 0 < Udivti3.divisor (called site s base) := by
    simpa [Udivti3.divisor, called, state_simp_rules] using hd
  have h := Udivti3.result_quotient (called site s base) _ pq dq
  simpa [callResult, Udivti3.numerator, Udivti3.divisor, called, state_simp_rules] using h

end SszArm.NatDivision
