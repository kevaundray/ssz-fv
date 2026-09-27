import SszArm.NatAddLargeCorrectAllocation

namespace SszArm.NatAdd.LargeCorrect

open SszNative
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- All dynamic-layout and reservation failures return through the actual
PC1248 error stores and RET, without changing the original arena cursor. -/
theorem error_finish (s u : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right)
    (failed : outcome s left right =
      NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted))
    (hc : CodeAt u base) (he : read_err u = .None) (ha : CheckSPAlignment u)
    (hp : read_pc u = base + 1248#64)
    (frame : Frame s u) (memory : MemoryFrame (localWrites s) s u) :
    ∃ fuel t, run fuel u = t ∧ Post s t left right := by
  let t := errorResult .scratch base u
  obtain ⟨trun, returned, image, tail⟩ := error_run_contract .scratch u base hc he ha hp
    (frame.return_owned owned.return_owned)
  have localEq : localWrites u = localWrites s := by
    simp only [localWrites, frame.out, frame.sp]
  have total : MemoryFrame (localWrites s) s t :=
    memory.trans (by simpa only [localEq] using tail)
  have cursorAddress : (r (.GPR 5#5) s + 16#64).toNat =
      (r (.GPR 5#5) s).toNat + 16 := by have := owned.arenaBound; bv_omega
  have cursor : (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t).toNat =
      (outcome s left right).used := by
    rw [total.read _ 8 (by rw [cursorAddress]; have := owned.arenaBound; omega)
      (by rw [cursorAddress]; exact owned.arenaLocal.subspan 16 8 (by decide))]
    simp only [failed, NatArithmetic.unchanged, arenaOf]
  refine ⟨50, t, trun, post_of_frame s t left right owned (frame.returned returned)
    ?_ ?_ cursor ?_⟩
  · simpa only [failed, NatArithmetic.unchanged, frame.out] using image
  · intro reservation impossible
    simp only [failed, NatArithmetic.unchanged] at impossible
    contradiction
  · simpa only [failed, NatArithmetic.unchanged, writesFor] using total

end SszArm.NatAdd.LargeCorrect
