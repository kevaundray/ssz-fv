import SszArm.NatDivisionSmallPost

namespace SszArm.NatDivision

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem cursor_local_preserved {original s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (frame : MemoryFrame (localWrites original) s t)
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) s).toNat =
      (outcome original operand).used) :
    (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) t).toNat =
      (outcome original operand).used := by
  have physical := owned.arenaBound
  have address : (r (.GPR 4#5) original + 16#64).toNat =
      (r (.GPR 4#5) original).toNat + 16 := by bv_omega
  rw [frame.read _ 8 (by rw [address]; omega)]
  · exact cursor
  · rw [address]
    exact owned.arenaLocal.subspan 16 8 (by decide)

/-- The successful width-two allocation takes this exact native suffix. Full
scratch observations are retained independently of the result's normalized form. -/
theorem wide_result_post (original s : ArmState) (base : BitVec 64)
    (operand quotient : SszNative.NatOperand) (remainder : BitVec 64)
    (owned : Owned original operand) (saved : Saved original s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 768#64)
    (success : (outcome original operand).result = .ok (quotient, remainder))
    (pointer : r (.GPR 9#5) s = quotient.pointer)
    (payload : r (.GPR 10#5) s = quotient.payload)
    (rem : r (.GPR 22#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s = remainder)
    (quotientAt : quotient.At (widthLoad s))
    (quotientOwned : OperandOwned (returnWrites s) quotient)
    (written : WrittenAt (widthLoad s) (outcome original operand))
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) s).toNat =
      (outcome original operand).used)
    (before : MemoryFrame (writesFor original (outcome original operand)) original s) :
    Post original (run 24 s) operand := by
  have space := owned.return_space saved.sp out
  let t := block base fastOutputOps s
  have args := fast_output_arguments s base space
  have localMemory := output_local_frame owned saved out (fast_output_frame s base space)
  have ready : ReturnReady t (outcome original operand).result := by
    rw [success]
    exact fast_output_ready s base space quotient remainder pointer payload rem quotientAt quotientOwned
  have code : CodeAt t base := by simpa only [t, CodeAt, block_program] using hc
  have error : read_err t = .None := (block_error _ _ _).trans he
  have aligned : CheckSPAlignment t := block_aligned _ _ _ ha
  rw [show 24 = 11 + 13 by decide, run_plus, fast_output_run s base hc he ha hp]
  exact finish_post original t base operand owned
    (fast_output_saved original s base saved owned.stackBound space)
    (args.2.2.2.2.1.trans out) code error aligned args.1 ready
    (written_local_preserved owned localMemory written)
    (cursor_local_preserved owned localMemory cursor)
    (before.trans (local_frame_for (outcome original operand) localMemory))

/-- After the complete quotient normalization scan, only the payload and the
shared remainder/status/restore suffix remain. This executes those 16 instructions. -/
theorem normalized_result_post (original s : ArmState) (base : BitVec 64)
    (operand quotient : SszNative.NatOperand) (remainder : BitVec 64)
    (owned : Owned original operand) (saved : Saved original s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 800#64)
    (success : (outcome original operand).result = .ok (quotient, remainder))
    (pointer : read_mem_bytes 8 (r (.GPR 19#5) s) s = quotient.pointer)
    (payload : r (.GPR 10#5) s = quotient.payload)
    (rem : r (.GPR 1#5) s = remainder)
    (status : (r (.GPR 8#5) s).setWidth 32 = 0#32)
    (quotientAt : quotient.At (widthLoad s))
    (quotientOwned : OperandOwned (returnWrites s) quotient)
    (written : WrittenAt (widthLoad s) (outcome original operand))
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) s).toNat =
      (outcome original operand).used)
    (before : MemoryFrame (writesFor original (outcome original operand)) original s) :
    Post original (run 16 s) operand := by
  have space := owned.return_space saved.sp out
  let t := block base payloadOps s
  have args := payload_arguments s base
  have localMemory := output_local_frame owned saved out (payload_frame s base space)
  have ready : ReturnReady t (outcome original operand).result := by
    rw [success]
    exact payload_ready s base space quotient remainder pointer payload rem status quotientAt quotientOwned
  have code : CodeAt t base := by simpa only [t, CodeAt, block_program] using hc
  have error : read_err t = .None := (block_error _ _ _).trans he
  have aligned : CheckSPAlignment t := block_aligned _ _ _ ha
  rw [show 16 = 3 + 13 by decide, run_plus, payload_run s base hc he ha hp]
  exact finish_post original t base operand owned
    (payload_saved original s base saved owned.stackBound space)
    (args.2.2.2.2.1.trans out) code error aligned args.1 ready
    (written_local_preserved owned localMemory written)
    (cursor_local_preserved owned localMemory cursor)
    (before.trans (local_frame_for (outcome original operand) localMemory))

end SszArm.NatDivision
