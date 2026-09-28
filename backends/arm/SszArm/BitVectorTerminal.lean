import SszArm.BitVectorReturnMemory
import SszArm.BitVectorStageState

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- A reached common-epilogue frontier. Resource observations are transported
separately so every previously committed allocation survives all later errors. -/
structure Terminal (s t : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (result : Except SszNative.BitVector.Error (BitVec 128)) : Prop where
  pc : read_pc t = base + 4732#64
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  resultAt : SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat data result

theorem Terminal.aligned {s t : ArmState} {base : BitVec 64} {data : Ssz.Bytes}
    {result : Except SszNative.BitVector.Error (BitVec 128)}
    (current : Terminal s t base data result) (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, current.sp] using aligned

/-- Execute the shared physical epilogue after any body exit, preserving the
entire resource result rather than rolling scratch back on an error. -/
theorem Terminal.finish {s t : ArmState} {base : BitVec 64} {length : SszNative.NatOperand}
    {data : Ssz.Bytes} (owned : Owned s length data)
    (current : Terminal s t base data (outcome s length data).result)
    (code : CodeAt t base) (aligned : CheckSPAlignment s)
    (written : (outcome s length data).writtenAt (widthLoad t))
    (cursor : (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) t).toNat = (outcome s length data).used)
    (arenaBase : read_mem_bytes 8 (r (.GPR 19#5) s) t = read_mem_bytes 8 (r (.GPR 19#5) s) s)
    (arenaCapacity : read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t =
      read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s)
    (frame : MemoryFrame (writesFor s (outcome s length data)) s t) :
    Post s (run 8 t) length data := by
  rw [epilogue t base code current.pc current.error (current.aligned aligned)]
  have activation := activation_of_memory owned owned.activationOwned frame
  have returned := returned_of_activation s t current.sp current.error activation current.vectors
  apply post_of_frame s (BoolCodec.returned t) length data owned returned
  · rw [return_observe]
    exact current.resultAt
  · rw [return_observe]
    exact written
  · simpa only [BoolCodec.returned, state_simp_rules] using cursor
  · simpa only [BoolCodec.returned, state_simp_rules] using arenaBase
  · simpa only [BoolCodec.returned, state_simp_rules] using arenaCapacity
  · simpa only [MemoryFrame, BoolCodec.returned_mem] using frame

end SszArm.BitVector
