import SszArm.NatMulLoopStore

namespace SszArm.NatMul

open Delimited (MemoryFrame)

theorem loop_stored_registers (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.GPR reg) (loopStored site s base) = r (.GPR reg) s := by
  simp [loopStored, loopStoreMemory, NatCompare.saved, state_simp_rules]

theorem loop_stored_flags (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (flag : PFlag) : r (.FLAG flag) (loopStored site s base) = r (.FLAG flag) s := by
  simp [loopStored, loopStoreMemory, NatCompare.saved, state_simp_rules]

theorem loop_stored_vectors (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (loopStored site s base) = r (.SFP reg) s := by
  simp [loopStored, loopStoreMemory, NatCompare.saved, state_simp_rules]

theorem loop_stored_program (site : LoopStoreSite) (s : ArmState) (base : BitVec 64) :
    (loopStored site s base).program = s.program := by
  simp [loopStored, loopStoreMemory, NatCompare.saved, state_simp_rules]

theorem loop_stored_error (site : LoopStoreSite) (s : ArmState) (base : BitVec 64) :
    read_err (loopStored site s base) = read_err s := by
  simp [loopStored, loopStoreMemory, NatCompare.saved, state_simp_rules]

theorem loop_stored_pc (site : LoopStoreSite) (s : ArmState) (base : BitVec 64) :
    read_pc (loopStored site s base) = base + BitVec.ofNat 64 (site.start + 32) := by
  simp [loopStored, state_simp_rules]

theorem loop_stored_memory (site : LoopStoreSite) (s : ArmState) (base : BitVec 64) :
    (loopStored site s base).mem =
      (write_mem_bytes 8 (site.address s) (r (.GPR site.source) s)
        (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s)).mem := by
  simp only [loopStored, loopStoreMemory, NatCompare.saved, ArmState.mem_w_eq_mem]

theorem loop_stored_word (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (physical : (site.address s).toNat + 8 ≤ 2^64) :
    read_mem_bytes 8 (site.address s) (loopStored site s base) = r (.GPR site.source) s := by
  simp only [loopStored, read_mem_bytes_of_w, loopStoreMemory]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ physical

theorem loop_stored_spill (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (site.address s).toNat + 8 ≤ 2^64)
    (separate : (site.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (site.address s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (loopStored site s base) = r (.GPR 9#5) s := by
  simp only [loopStored, read_mem_bytes_of_w]
  exact loop_store_restore site s stack physical separate

theorem loop_stored_frame (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (site.address s).toNat + 8 ≤ 2^64) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 8), ((site.address s).toNat, 8)]
      s (loopStored site s base) := by
  intro address outside
  have spill := outside ((r (.GPR 31#5) s).toNat - 16, 8) (by simp)
  have word := outside ((site.address s).toNat, 8) (by simp)
  rw [loop_stored_memory]
  exact (BoolCodec.write_mem_bytes_frame (NatCompare.saved s 9#5) (site.address s) 8
    (r (.GPR site.source) s) address physical word).trans
    (BoolCodec.write_mem_bytes_frame s _ 8 _ address (by bv_omega) (by bv_omega))

end SszArm.NatMul
