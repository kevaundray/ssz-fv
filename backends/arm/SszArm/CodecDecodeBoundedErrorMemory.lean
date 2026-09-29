import SszArm.CodecDecodeBoundedErrorStages
import SszArm.NatCompareMemory
import SszArm.UintResultMemory

namespace SszArm.Codec.Decode.Bounded

open Delimited (Span MemoryFrame)

/-- Exact memories, including both lowering spills and reload-dependent pair
contents. This definition deliberately makes no output/scratch disjointness assumption. -/
def ErrorStage.memory (stage : ErrorStage) (s : ArmState) : ArmState :=
  let out := r (.GPR 19#5) s
  let sp := r (.GPR 31#5) s
  match stage with
  | .expected => write_mem_bytes 16 (out + 16#64)
      (r (.GPR 22#5) s ++ r (.GPR 21#5) s) s
  | .tag =>
      let scratch := write_mem_bytes 8 (sp - 8#64) (r (.GPR 10#5) s)
        (write_mem_bytes 8 (sp - 16#64) (r (.GPR 9#5) s) s)
      write_mem_bytes 8 (out + 8#64) 0#64 (write_mem_bytes 8 out (r (.GPR 8#5) s) scratch)
  | .actual =>
      let low := read_mem_bytes 8 (r (.GPR 20#5) s) s
      let high := read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) s
      let scratch := write_mem_bytes 8 (sp - 8#64) (r (.GPR 10#5) s)
        (write_mem_bytes 8 (sp - 16#64) high s)
      let zeros := write_mem_bytes 8 (out + 56#64) 0#64
        (write_mem_bytes 8 (out + 48#64) 0#64 scratch)
      write_mem_bytes 4 (out + 64#64) 2#32
        (write_mem_bytes 16 (out + 32#64)
          (read_mem_bytes 8 (sp - 16#64) zeros ++ low) zeros)

@[simp] theorem error_stage_memory (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).mem = (stage.memory s).mem := by
  cases stage <;>
    simp [ErrorStage.result, ErrorStage.ops, ErrorStage.memory, block, Op.effect,
      put, next, loadPair, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      NatCompare.read_spill_w]
  all_goals
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes,
      Memory.State.read_mem_bytes_eq_mem_read_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem error_stage_vector (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (stage.result s base) = r (.SFP reg) s := by
  cases stage <;> simp [ErrorStage.result, ErrorStage.ops, block, Op.effect,
    put, next, loadPair, state_simp_rules]

def errorWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 19#5) s).toNat, 68)]

theorem error_stage_frame (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2 ^ 64) :
    MemoryFrame (errorWrites s) s (stage.result s base) := by
  intro address outside
  have scratch := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have result := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  simp only [Prod.fst, Prod.snd] at scratch result
  rw [error_stage_memory]
  cases stage <;>
    simp (disch := bv_omega) only [ErrorStage.memory, BoolCodec.write_mem_bytes_frame]

/-- The expected operand's physical record is copied verbatim; no Nat
normalization or inspection is performed by this stage. -/
theorem expected_pair (s : ArmState) (base : BitVec 64)
    (bound : (r (.GPR 19#5) s).toNat + 32 ≤ 2 ^ 64) :
    read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) (ErrorStage.expected.result s base) =
      r (.GPR 21#5) s ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 24#64) (ErrorStage.expected.result s base) =
      r (.GPR 22#5) s := by
  have pairSpace : (r (.GPR 19#5) s + 16#64).toNat + 16 ≤ 2 ^ 64 := by bv_omega
  simp only [Memory.mem_eq_iff_read_mem_bytes_eq.mp (error_stage_memory .expected s base),
    ErrorStage.memory]
  simp only [UintCodec.Tail.write_pair_words s (r (.GPR 19#5) s + 16#64)
    (r (.GPR 21#5) s) (r (.GPR 22#5) s) pairSpace]
  constructor <;>
    simp (disch := bv_omega) only [BitVec.add_assoc,
      show 16#64 + 8#64 = 24#64 from rfl,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

end SszArm.Codec.Decode.Bounded
