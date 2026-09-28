import SszArm.BitVectorContract
import SszArm.BitVectorProgram
import SszArm.NatDivisionProofs
import SszArm.NatAddProofs
import SszArm.NatExactProofs
import SszArm.NatToU128Proofs

namespace SszArm.BitVector

/-- The complete linked instruction closure, including division's __udivti3 and
all four concrete memcpy call sites. No execution proposition occurs here. -/
structure JointCodeAt (s : ArmState) (base : BitVec 64) : Prop where
  body : CodeAt s base
  division : NatDivision.JointCodeAt s (base + divisionOffset)
  add : NatAdd.CodeAt s (base + addOffset)
  exactLeaf : NatExact.CodeAt s (base + exactOffset)
  toU128 : NatToU128.CodeAt s (base + toU128Offset)
  memcpy : SszArm.CodeAt s (base + memcpyOffset) Memcpy.program

inductive CallSite where
  | divide | divisionError | round | roundTemporary | roundError | scope | scopeError | narrow
  deriving DecidableEq

def CallSite.offset : CallSite → Nat
  | .divide => 468
  | .divisionError => 504
  | .round => 3412
  | .roundTemporary => 3436
  | .roundError => 3456
  | .scope => 5960
  | .scopeError => 5984
  | .narrow => 6588

def CallSite.target : CallSite → BitVec 64
  | .divide => divisionOffset
  | .round => addOffset
  | .scope => exactOffset
  | .narrow => toU128Offset
  | _ => memcpyOffset

def CallSite.word : CallSite → BitVec 32
  | .divide => 0x97ffb349#32
  | .divisionError => 0x9400654e#32
  | .round => 0x97ffbb4e#32
  | .roundTemporary => 0x94006271#32
  | .roundError => 0x9400626c#32
  | .scope => 0x94000b33#32
  | .scopeError => 0x94005ff4#32
  | .narrow => 0x94000ae0#32

def called (site : CallSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + site.target)
    (w (.GPR 30#5) (base + BitVec.ofNat 64 (site.offset + 4)) s)

/-- This is the real linked BL, not an abstract external-call transition. -/
theorem call_step (site : CallSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    stepi s = called site s base := by
  have fetched := code (site.offset, site.word) (by cases site <;> decide)
  cases site <;> simp only [CallSite.offset, CallSite.word] at pc fetched ⊢
  all_goals
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    have hpc : r .PC s = _ := pc
    simp (config := {decide := true, instances := true})
      [exec_inst, called, CallSite.offset, CallSite.target, divisionOffset, addOffset,
       exactOffset, toU128Offset, memcpyOffset, state_simp_rules, bitvec_rules,
       minimal_theory, hpc, BitVec.add_assoc]

@[simp] theorem called_program (site : CallSite) (s : ArmState) (base : BitVec 64) :
    (called site s base).program = s.program := by
  simp only [called, state_simp_rules]

@[simp] theorem called_memory (site : CallSite) (s : ArmState) (base : BitVec 64) :
    (called site s base).mem = s.mem := by
  simp only [called, state_simp_rules]

@[simp] theorem called_error (site : CallSite) (s : ArmState) (base : BitVec 64) :
    read_err (called site s base) = read_err s := by
  simp (config := {decide := true}) [called, state_simp_rules]

@[simp] theorem called_pc (site : CallSite) (s : ArmState) (base : BitVec 64) :
    read_pc (called site s base) = base + site.target := by
  simp only [called, state_simp_rules]

theorem called_aligned (site : CallSite) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (called site s base) := by
  simpa (config := {decide := true}) [CheckSPAlignment, called, state_simp_rules] using aligned

theorem JointCodeAt.called {s : ArmState} {base : BitVec 64}
    (code : JointCodeAt s base) (site : CallSite) : JointCodeAt (called site s base) base := by
  rcases code with ⟨body, division, add, exactLeaf, narrow, memcpy⟩
  constructor
  · simpa only [CodeAt, called_program] using body
  · simpa only [NatDivision.JointCodeAt, NatDivision.CodeAt, Udivti3.CodeAt,
      SszArm.CodeAt, called_program] using division
  · simpa only [NatAdd.CodeAt, called_program] using add
  · simpa only [NatExact.CodeAt, called_program] using exactLeaf
  · simpa only [NatToU128.CodeAt, called_program] using narrow
  · simpa only [SszArm.CodeAt, called_program] using memcpy

theorem JointCodeAt.of_program {s t : ArmState} {base : BitVec 64}
    (code : JointCodeAt s base) (program : t.program = s.program) : JointCodeAt t base := by
  rcases code with ⟨body, division, add, exactLeaf, narrow, memcpy⟩
  constructor
  · simpa only [CodeAt, program] using body
  · simpa only [NatDivision.JointCodeAt, NatDivision.CodeAt, Udivti3.CodeAt,
      SszArm.CodeAt, program] using division
  · simpa only [NatAdd.CodeAt, program] using add
  · simpa only [NatExact.CodeAt, program] using exactLeaf
  · simpa only [NatToU128.CodeAt, program] using narrow
  · simpa only [SszArm.CodeAt, program] using memcpy

theorem JointCodeAt.run {s : ArmState} {base : BitVec 64}
    (code : JointCodeAt s base) (fuel : Nat) : JointCodeAt (run fuel s) base :=
  code.of_program (run_program fuel s)

/-- Entry through the real division BL and the linked helper/runtime RETs. -/
theorem divide_call (s : ArmState) (base : BitVec 64) (length : SszNative.NatOperand)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 468#64)
    (owned : NatDivision.Owned (called .divide s base) length) :
    ∃ fuel t, run fuel s = t ∧ NatDivision.Post (called .divide s base) t length := by
  obtain ⟨fuel, post⟩ := NatDivision.program_correct (called .divide s base)
    (base + divisionOffset) length owned (code.called .divide).division
    (by simpa only [called_error] using error) (called_aligned _ _ _ aligned)
    (by simp only [called_pc, CallSite.target])
  refine ⟨fuel + 1, run fuel (called .divide s base), ?_, post⟩
  rw [run, call_step .divide s base code.body error (by exact pc)]

/-- Optional ceiling increment, with the full allocation/failure postcondition. -/
theorem round_call (s : ArmState) (base : BitVec 64) (quotient : SszNative.NatOperand)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3412#64)
    (owned : NatAdd.Owned (called .round s base) quotient (.small 1)) :
    ∃ fuel t, run fuel s = t ∧ NatAdd.Post (called .round s base) t quotient (.small 1) := by
  obtain ⟨fuel, t, execution, post⟩ := NatAdd.add_correct (called .round s base)
    (base + addOffset) quotient (.small 1) owned (code.called .round).add
    (by simpa only [called_error] using error) (called_aligned _ _ _ aligned)
    (by simp only [called_pc, CallSite.target, NatAdd.entry, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero])
  refine ⟨fuel + 1, t, ?_, post⟩
  rw [run, call_step .round s base code.body error (by exact pc), execution]

/-- Exact scope check retains the original expected representation on failure. -/
theorem scope_call (s : ArmState) (base : BitVec 64) (expected : SszNative.NatOperand)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 5960#64)
    (owned : NatExact.Owned (called .scope s base) expected) :
    ∃ fuel t, run fuel s = t ∧ NatExact.Post (called .scope s base) t expected := by
  obtain ⟨fuel, t, execution, post⟩ := NatExact.exact_correct (called .scope s base)
    (base + exactOffset) expected owned (code.called .scope).exactLeaf
    (by simpa only [called_error] using error) (called_aligned _ _ _ aligned)
    (by simp only [called_pc, CallSite.target])
  refine ⟨fuel + 1, t, ?_, post⟩
  rw [run, call_step .scope s base code.body error (by exact pc), execution]

/-- Full to_u128 execution; no bounded-value premise replaces its native scan. -/
theorem narrow_call (s : ArmState) (base : BitVec 64) (length : SszNative.NatOperand)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6588#64)
    (owned : NatToU128.Owned (called .narrow s base) length) :
    ∃ fuel t, run fuel s = t ∧ NatToU128.Post (called .narrow s base) t length := by
  obtain ⟨fuel, t, execution, post⟩ := NatToU128.to_u128_correct (called .narrow s base)
    (base + toU128Offset) length owned (code.called .narrow).toU128
    (by simpa only [called_error] using error) (called_aligned _ _ _ aligned)
    (by simp only [called_pc, CallSite.target, NatToU128.entry, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero])
  refine ⟨fuel + 1, t, ?_, post⟩
  rw [run, call_step .narrow s base code.body error (by exact pc), execution]

/-- Each memcpy call executes the bound runtime implementation. Its result is an
opaque state summary; subsequent observations use Memcpy.result_memory/frame. -/
theorem memcpy_call (site : CallSite) (s : ArmState) (base : BitVec 64)
    (runtime : site = .divisionError ∨ site = .roundTemporary ∨ site = .roundError ∨
      site = .scopeError)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s =
      Memcpy.result (called site s base) := by
  have target : site.target = memcpyOffset := by
    rcases runtime with rfl | rfl | rfl | rfl <;> rfl
  rw [run, call_step site s base code.body error pc]
  have count : r (.GPR 2#5) (called site s base) = r (.GPR 2#5) s := by
    simp (config := {decide := true}) [called, state_simp_rules]
  rw [← count]
  exact Memcpy.program_run _ _ (code.called site).memcpy
    (by simp only [called_pc, target]) (by simpa only [called_error] using error)

end SszArm.BitVector
