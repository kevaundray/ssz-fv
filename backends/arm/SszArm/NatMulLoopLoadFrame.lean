import SszArm.NatMulLoopLoad
import SszArm.DelimitedMemory

namespace SszArm.NatMul

open Delimited (MemoryFrame)

theorem loop_loaded_value (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    r (.GPR site.destination) (loopLoaded site s base value) = value := by
  simp [loopLoaded, state_simp_rules]

theorem loop_loaded_registers (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64)
    (reg : BitVec 5) (different : reg ≠ site.destination) :
    r (.GPR reg) (loopLoaded site s base value) = r (.GPR reg) s := by
  simp [loopLoaded, NatCompare.saved, state_simp_rules, different]

theorem loop_loaded_stack (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    r (.GPR 31#5) (loopLoaded site s base value) = r (.GPR 31#5) s :=
  loop_loaded_registers site s base value _ (by cases site <;> decide)

theorem loop_loaded_flags (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64)
    (flag : PFlag) : r (.FLAG flag) (loopLoaded site s base value) = r (.FLAG flag) s := by
  simp [loopLoaded, NatCompare.saved, state_simp_rules]

theorem loop_loaded_vectors (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (loopLoaded site s base value) = r (.SFP reg) s := by
  simp [loopLoaded, NatCompare.saved, state_simp_rules]

theorem loop_loaded_program (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    (loopLoaded site s base value).program = s.program := by
  simp [loopLoaded, NatCompare.saved, state_simp_rules]

theorem loop_loaded_error (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    read_err (loopLoaded site s base value) = read_err s := by
  simp [loopLoaded, NatCompare.saved, state_simp_rules]

theorem loop_loaded_pc (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    read_pc (loopLoaded site s base value) = base + BitVec.ofNat 64 (site.start + 32) := by
  simp [loopLoaded, state_simp_rules]

theorem loop_loaded_memory (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    (loopLoaded site s base value).mem =
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s).mem := by
  simp only [loopLoaded, NatCompare.saved, ArmState.mem_w_eq_mem]

theorem loop_loaded_spill (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (loopLoaded site s base value) =
      r (.GPR 9#5) s := by
  simp only [loopLoaded, read_mem_bytes_of_w, NatCompare.saved]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)

theorem loop_loaded_frame (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 8)] s (loopLoaded site s base value) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 8) (by simp)
  rw [loop_loaded_memory]
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ address (by bv_omega) (by bv_omega)

end SszArm.NatMul
