import SszArm.CodecDecodeBoundedOps
import SszArm.EmitActivationReturnStatus

namespace SszArm.Codec.Decode.Bounded

open Delimited (Span MemoryFrame)

def statusOps : List Op :=
  [.p196, .p200, .p204, .p208, .p212, .p216, .p220, .p224, .p228, .p232]

/-- These ten linked bounded instructions have exactly the checked emitter
status-store effects, including both real lowering spills. No code-map
substitution or emitter execution hypothesis is involved. -/
theorem status_effect (s : ArmState) (base : BitVec 64) :
    block base statusOps s = Emit.statusStored s := by
  unfold block statusOps Emit.statusStored Emit.ReturnBlock.block Emit.statusOps
  rfl

theorem status_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 196#64) : run 10 s = Emit.statusStored s := by
  have follows : Follows base statusOps s := by
    change r .PC s = _ at pc
    simp [statusOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      pc, BitVec.add_assoc]
  exact (block_run base statusOps s code error aligned follows).trans (status_effect s base)

def statusWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 19#5) s).toNat + 64, 4)]

theorem status_frame (s : ArmState)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2 ^ 64) :
    MemoryFrame (statusWrites s) s (Emit.statusStored s) := by
  intro address outside
  have scratch := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [statusWrites])
  have status := outside ((r (.GPR 19#5) s).toNat + 64, 4) (by simp [statusWrites])
  simp only [Prod.fst, Prod.snd] at scratch status
  rw [Emit.statusStored_memory]
  simp only [Emit.statusMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 4 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)

end SszArm.Codec.Decode.Bounded
