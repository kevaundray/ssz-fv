import SszArm.NatMulWordExec
import SszArm.NatCompareBlocks
import SszArm.NatAddLoopMemory

namespace SszArm.NatMulWord

open Delimited (MemoryFrame)

def storeOps : List Op := [.p752, .p756, .p760, .p764, .p768, .p772, .p776, .p780]

def storeAddress (s : ArmState) : BitVec 64 :=
  r (.GPR 15#5) s + (r (.GPR 13#5) s <<< 3)

def storeMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (storeAddress s) (r (.GPR 18#5) s) (NatCompare.saved s 9#5)

theorem store_effect (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (storeAddress s).toNat + 8 ≤ 2^64)
    (separate : (storeAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (storeAddress s).toNat) :
    block base storeOps s = w .PC (read_pc s + 32#64) (storeMemory s) := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (storeMemory s) = r (.GPR 9#5) s := by
    unfold storeMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) physical (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  change NatAdd.indexedStoreSequence s 15#5 13#5 9#5 18#5 = _
  exact NatAdd.indexedStoreSequence_eq s 15#5 13#5 9#5 18#5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) restored

theorem store_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 752#64) : run 8 s = block base storeOps s := by
  apply block_run base storeOps s code error aligned
  have hpc : r .PC s = base + 752#64 := pc
  simp [Follows, storeOps, Op.row, Op.effect, put, next, state_simp_rules,
    hpc, BitVec.add_assoc]

theorem stored_word (s : ArmState) (physical : (storeAddress s).toNat + 8 ≤ 2^64) :
    read_mem_bytes 8 (storeAddress s) (storeMemory s) = r (.GPR 18#5) s :=
  BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ physical

theorem store_frame (s : ArmState)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (storeAddress s).toNat + 8 ≤ 2^64) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16), ((storeAddress s).toNat, 8)]
      s (storeMemory s) := by
  intro address outside
  have stackOutside := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  have destinationOutside := outside ((storeAddress s).toNat, 8) (by simp)
  simp (disch := bv_omega) [storeMemory, NatCompare.saved, BoolCodec.write_mem_bytes_frame]

end SszArm.NatMulWord
