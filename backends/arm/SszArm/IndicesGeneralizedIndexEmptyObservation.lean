import SszArm.IndicesGeneralizedIndexEmptyMemory

namespace SszArm.Indices.GeneralizedIndex.Empty

open Dispatch.Block (next put save branch)

theorem emptyReturned_memory (s : ArmState) (owned : Owned s) :
    (emptyReturned s).mem = (emptyMemory s).mem := by
  have low := owned.stackLow
  have bound := owned.outputBound
  have apart := output_stack_apart s owned
  have spBound := (r (.GPR 31#5) s).isLt
  have h16 := stackSlot_toNat s owned 16 (by decide)
  have h32 := stackSlot_toNat s owned 32 (by decide)
  have h48 := stackSlot_toNat s owned 48 (by decide)
  have h64 := stackSlot_toNat s owned 64 (by decide)
  have h80 := stackSlot_toNat s owned 80 (by decide)
  have h232 := stackSlot_toNat s owned 232 (by decide)
  have h240 := stackSlot_toNat s owned 240 (by decide)
  have h8 := output_toNat s owned 8 (by decide)
  have hOut64 := output_toNat s owned 64 (by decide)
  simp (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
    BitVec.add_assoc] at h16 h32 h48 h64 h80 h232 h240 h8 hOut64
  simp (disch := (simp only [h16, h32, h48, h64, h80, h232, h240, h8, hOut64]; omega))
    [emptyReturned, emptyOps, block, Op.effect, next, put, save, branch, loadPair,
     emptyMemory, stackSlot, state_simp_rules, BitVec.sub_eq_add_neg, BitVec.add_assoc,
     BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem emptyReturned_frame (s : ArmState) (owned : Owned s) :
    Delimited.MemoryFrame (emptyWrites s) s (emptyReturned s) := by
  intro address outside
  rw [emptyReturned_memory s owned]
  exact emptyMemory_frame s owned address outside

end SszArm.Indices.GeneralizedIndex.Empty
