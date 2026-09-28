import SszArm.MeasureBitsPropagationExec

namespace SszArm.Measure.Bits.Propagation

open Delimited (MemoryFrame)

@[simp] theorem stage_program (stage : Stage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).program = s.program := by
  cases stage <;> simp [Stage.result, state_simp_rules]

@[simp] theorem stage_error (stage : Stage) (s : ArmState) (base : BitVec 64) :
    read_err (stage.result s base) = read_err s := by
  cases stage <;> simp [Stage.result, state_simp_rules]

@[simp] theorem stage_sp (stage : Stage) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (stage.result s base) = r (.GPR 31#5) s := by
  cases stage <;> simp [Stage.result, state_simp_rules]

@[simp] theorem stage_vector (stage : Stage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (stage.result s base) = r (.SFP reg) s := by
  cases stage <;> simp [Stage.result, state_simp_rules]

def Stage.clobbers : Stage → List (BitVec 5)
  | .returned => [20#5, 21#5, 22#5]
  | .prepare => [0#5, 1#5, 2#5]
  | .finish => [8#5]

theorem stage_register (stage : Stage) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (untouched : reg ∉ stage.clobbers) :
    r (.GPR reg) (stage.result s base) = r (.GPR reg) s := by
  cases stage <;>
    simp only [Stage.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched <;>
    simp (disch := simp_all) [Stage.result, state_simp_rules]

@[simp] theorem returned_memory (s : ArmState) (base : BitVec 64) :
    (Stage.returned.result s base).mem = s.mem := by
  simp [Stage.result, state_simp_rules]

@[simp] theorem prepare_memory (s : ArmState) (base : BitVec 64) :
    (Stage.prepare.result s base).mem = s.mem := by
  simp [Stage.result, state_simp_rules]

theorem finish_frame (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    MemoryFrame [((r (.GPR 19#5) s).toNat, 16),
      ((r (.GPR 19#5) s).toNat + 64, 8)] s (Stage.finish.result s base) := by
  intro address outside
  have first := outside ((r (.GPR 19#5) s).toNat, 16) (by simp)
  have last := outside ((r (.GPR 19#5) s).toNat + 64, 8) (by simp)
  have statusNat : (r (.GPR 19#5) s + 64#64).toNat = (r (.GPR 19#5) s).toNat + 64 := by
    bv_omega
  simp only [Stage.result, ArmState.mem_w_eq_mem]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by rw [statusNat]; omega)
    (by simpa only [statusNat] using last)]
  exact BoolCodec.write_mem_bytes_frame s _ 16 _ address (by omega) first

/-- The final STP uses two 32-bit words, unlike the native Nat pair stores. -/
theorem write_pair_dwords (s : ArmState) (address : BitVec 64) (lo hi : BitVec 32)
    (physical : address.toNat + 8 ≤ 2^64) :
    write_mem_bytes 8 address (hi ++ lo) s =
      write_mem_bytes 4 (address + 4#64) hi (write_mem_bytes 4 address lo s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    simp only [state_simp_rules]
  · simp only [state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    funext byte
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes]
    by_cases before : byte.toNat < address.toNat
    · rw [Memory.write_bytes_eq_of_le before physical,
        Memory.write_bytes_eq_of_le (by bv_omega) (by bv_omega),
        Memory.write_bytes_eq_of_le before (by omega)]
    · by_cases after : address.toNat + 8 ≤ byte.toNat
      · rw [Memory.write_bytes_eq_of_ge after physical,
          Memory.write_bytes_eq_of_ge (by bv_omega) (by bv_omega),
          Memory.write_bytes_eq_of_ge (by omega) (by omega)]
      · rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) physical]
        by_cases low : byte.toNat < address.toNat + 4
        · rw [Memory.write_bytes_eq_of_le (by bv_omega) (by bv_omega),
            Memory.write_bytes_eq_extractLsByte (by omega) low (by omega)]
          simp only [BitVec.extractLsByte_def]
          exact BitVec.extractLsb'_append_eq_of_add_le (by bv_omega)
        · rw [Memory.write_bytes_eq_extractLsByte (by bv_omega) (by bv_omega) (by bv_omega)]
          simp only [BitVec.extractLsByte_def]
          rw [BitVec.extractLsb'_append_eq_of_le (by bv_omega)]
          congr 1
          bv_omega

/-- The four-byte tail is read from SP+188, not initialized there. -/
theorem finish_tail (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    read_mem_bytes 4 (r (.GPR 19#5) s + 68#64) (Stage.finish.result s base) =
      read_mem_bytes 4 (r (.GPR 31#5) s + 188#64) s := by
  have statusPhysical : (r (.GPR 19#5) s + 64#64).toNat + 8 ≤ 2^64 := by bv_omega
  simp only [Stage.result, state_simp_rules]
  rw [show r (.GPR 19#5) s + 68#64 = (r (.GPR 19#5) s + 64#64) + 4#64 by bv_omega]
  rw [write_pair_dwords _ _ _ _ statusPhysical]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 4 _ _ (by bv_omega)

end SszArm.Measure.Bits.Propagation
