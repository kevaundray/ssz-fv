import Arm.Exec
import SszArm.Impl

/-!
# Execution, return, memory and ABI contracts

Every step theorem below uses LNSym's decoder with a kernel-checked `rfl` proof.
The code base, data address, stored value, initial memory, and caller's return
address are symbolic. No model example theorem or admitted theorem is used.

`loadProgram_run` and `storeProgram_run` give the entire final state, including
`ret`. The correctness theorems expose the result and frame: the store changes
only its eight data bytes and PC; the load changes only x0 and PC. In particular,
all callee-saved registers, SP, SIMD/FP registers and NZCV flags are preserved.
The instruction map is immutable and separate from data memory in LNSym.
-/

namespace SszArm

open BitVec

/-- Read-after-write proved from byte extraction, without the model's native-SAT
memory-separation lemmas. The caller's region does not wrap around address zero. -/
theorem read_write_bytes (s : ArmState) (n : Nat) (addr : BitVec 64)
    (value : BitVec (n * 8)) (hspace : addr.toNat + n ≤ 2 ^ 64) :
    read_mem_bytes n addr (write_mem_bytes n addr value s) = value := by
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.write_mem_bytes_eq_mem_write_bytes]
  apply BitVec.eq_of_extractLsByte_eq
  intro i
  by_cases hi : i < n
  · rw [Memory.extractLsByte_read_bytes hspace, if_pos hi]
    change s.mem.write_bytes n addr value (addr + BitVec.ofNat 64 i) = _
    have haddr : (addr + BitVec.ofNat 64 i).toNat = addr.toNat + i := by bv_omega
    rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) hspace]
    have hsub : (addr + BitVec.ofNat 64 i - addr).toNat = i := by bv_omega
    rw [hsub]
  · rw [BitVec.extractLsByte_ge (by omega), BitVec.extractLsByte_ge (by omega)]

theorem step_load (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0xf9400000#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (w (.GPR 0) (read_mem_bytes 8 (r (.GPR 0) s) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory, BitVec.setWidth_eq]
  rfl

theorem step_store (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0xf9000001#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 8 (r (.GPR 0) s) (r (.GPR 1) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory, BitVec.setWidth_eq]
  rfl

theorem step_ret (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0xd65f03c0#32) :
    stepi s = w .PC (r (.GPR 30) s) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory]

/-- Exact state after the load and return, at any symbolic program base. -/
theorem loadProgram_run (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base loadProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None) :
    run 2 s = w .PC (r (.GPR 30) s)
      (w .PC (base + 4#64) (w (.GPR 0) (read_mem_bytes 8 (r (.GPR 0) s) s) s)) := by
  have herr' : r .ERR s = .None := herr
  let s1 := w .PC (base + 4#64)
    (w (.GPR 0) (read_mem_bytes 8 (r (.GPR 0) s) s) s)
  have h1 : stepi s = s1 := by
    rw [step_load s herr (by simpa [hpc, loadProgram] using hcode 0 (by decide))]
    simp only [s1, hpc]
  have h2 : stepi s1 = w .PC (r (.GPR 30) s) s1 := by
    rw [step_ret s1 (by simp (config := {decide := true}) [s1, state_simp_rules, herr'])
      (by simpa (config := {decide := true}) [s1, state_simp_rules, loadProgram] using
        hcode 1 (by decide))]
    simp (config := {decide := true}) only [s1, state_simp_rules, minimal_theory]
  show stepi (stepi s) = _
  rw [h1, h2]

/-- Exact state after the store and return, including the actual model write. -/
theorem storeProgram_run (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base storeProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None) :
    run 2 s = w .PC (r (.GPR 30) s)
      (w .PC (base + 4#64) (write_mem_bytes 8 (r (.GPR 0) s) (r (.GPR 1) s) s)) := by
  have herr' : r .ERR s = .None := herr
  let s1 := w .PC (base + 4#64)
    (write_mem_bytes 8 (r (.GPR 0) s) (r (.GPR 1) s) s)
  have h1 : stepi s = s1 := by
    rw [step_store s herr (by simpa [hpc, storeProgram] using hcode 0 (by decide))]
    simp only [s1, hpc]
  have h2 : stepi s1 = w .PC (r (.GPR 30) s) s1 := by
    rw [step_ret s1 (by simp (config := {decide := true}) [s1, state_simp_rules, herr'])
      (by simpa (config := {decide := true}) [s1, state_simp_rules, storeProgram] using
        hcode 1 (by decide))]
    simp (config := {decide := true}) only [s1, state_simp_rules, minimal_theory]
  show stepi (stepi s) = _
  rw [h1, h2]

/-- Load result, return and complete state frame. No memory is changed. -/
theorem loadProgram_correct (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base loadProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None) :
    let s' := run 2 s
    r (.GPR 0) s' = read_mem_bytes 8 (r (.GPR 0) s) s ∧
      read_err s' = .None ∧ read_pc s' = r (.GPR 30) s ∧
      s'.mem = s.mem ∧ s'.program = s.program ∧
      (∀ f, f ≠ .GPR 0 → f ≠ .PC → r f s' = r f s) := by
  intro s'
  simp only [s', loadProgram_run s base hcode hpc herr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [state_simp_rules]
  · simp [state_simp_rules, show r .ERR s = .None from herr]
  · simp [state_simp_rules]
  · simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro f h0 hpc'
    rw [r_of_w_different hpc', r_of_w_different hpc', r_of_w_different h0]

/-- Store result, return and complete frame outside the non-wrapping output region. -/
theorem storeProgram_correct (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base storeProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None)
    (hspace : (r (.GPR 0) s).toNat + 8 ≤ 2 ^ 64) :
    let s' := run 2 s
    read_mem_bytes 8 (r (.GPR 0) s) s' = r (.GPR 1) s ∧
      read_err s' = .None ∧ read_pc s' = r (.GPR 30) s ∧
      s'.program = s.program ∧
      (∀ f, f ≠ .PC → r f s' = r f s) ∧
      (∀ addr : BitVec 64, addr.toNat < (r (.GPR 0) s).toNat ∨
        (r (.GPR 0) s).toNat + 8 ≤ addr.toNat → s'.mem addr = s.mem addr) := by
  intro s'
  simp only [s', storeProgram_run s base hcode hpc herr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [read_mem_bytes_of_w]
    exact read_write_bytes s 8 (r (.GPR 0) s) (r (.GPR 1) s) hspace
  · simp [state_simp_rules, show r .ERR s = .None from herr]
  · simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro f hpc'
    rw [r_of_w_different hpc', r_of_w_different hpc', r_of_write_mem_bytes]
  · intro addr outside
    simp only [ArmState.mem_w_eq_mem, Memory.write_mem_bytes_eq_mem_write_bytes]
    rcases outside with before | after
    · exact Memory.write_bytes_eq_of_le before hspace
    · exact Memory.write_bytes_eq_of_ge after hspace

/-- The load's code-placement precondition has a witness for every base. -/
theorem codeAt_loadProgram (s : ArmState) (base : BitVec 64)
    (h : s.program = loadAt base loadProgram) : CodeAt s base loadProgram := by
  intro k hk
  rw [h]
  simp only [loadProgram, List.length_cons, List.length_nil] at hk
  match k, hk with
  | 0, _ | 1, _ => simp [loadAt, loadProgram, Map.find?]

/-- The store's code-placement precondition has a witness for every base. -/
theorem codeAt_storeProgram (s : ArmState) (base : BitVec 64)
    (h : s.program = loadAt base storeProgram) : CodeAt s base storeProgram := by
  intro k hk
  rw [h]
  simp only [storeProgram, List.length_cons, List.length_nil] at hk
  match k, hk with
  | 0, _ | 1, _ => simp [loadAt, storeProgram, Map.find?]

end SszArm
