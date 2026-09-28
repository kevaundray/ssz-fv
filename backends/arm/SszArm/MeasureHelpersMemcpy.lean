import SszArm.MeasureHelpersCalls
import SszArm.BitVectorMemcpy

namespace SszArm.Measure.Helpers

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

theorem memcpy_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1940#64) :
    run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s =
      Memcpy.result (called .propagateError s base) := by
  rw [run, call_step .propagateError s base code error pc]
  have runtime : SszArm.CodeAt (called .propagateError s base)
      (base + memcpyOffset) Memcpy.program := by
    simpa only [SszArm.CodeAt, called_program] using memcpy_codeAt code
  have start : read_pc (called .propagateError s base) = base + memcpyOffset :=
    called_pc _ _ _
  have count : r (.GPR 2#5) (called .propagateError s base) = r (.GPR 2#5) s :=
    called_register _ _ _ _ (by decide)
  rw [← count]
  exact Memcpy.program_run _ _ runtime start ((called_error _ _ _).trans error)

/-- The real propagation BL copies only the 48-byte error payload. Its caller
writes the two leading words and the status/tail pair separately. -/
structure CopyPost (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 1944#64
  program : t.program = s.program
  error : read_err t = .None
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  copied : ∀ offset bytes, offset + bytes ≤ (r (.GPR 2#5) s).toNat →
    widthLoad t ((r (.GPR 0#5) s).toNat + offset) bytes =
      widthLoad s ((r (.GPR 1#5) s).toNat + offset) bytes
  frame : MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s t

theorem memcpy_correct (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1940#64)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s)
      (r (.GPR 2#5) s).toNat) :
    CopyPost s (run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s) base := by
  rw [memcpy_run s base code error pc]
  let c := called .propagateError s base
  have r0 : r (.GPR 0#5) c = r (.GPR 0#5) s := called_register _ _ _ _ (by decide)
  have r1 : r (.GPR 1#5) c = r (.GPR 1#5) s := called_register _ _ _ _ (by decide)
  have r2 : r (.GPR 2#5) c = r (.GPR 2#5) s := called_register _ _ _ _ (by decide)
  have dst : (r (.GPR 0#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r0, r2]
  have src : (r (.GPR 1#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r1, r2]
  have sep : Memcpy.Disjoint (r (.GPR 0#5) c) (r (.GPR 1#5) c)
      (r (.GPR 2#5) c).toNat := by rwa [r0, r1, r2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have returned := Memcpy.result_return c
    simpa [c, called, CallSite.offset, state_simp_rules] using returned
  · exact (Memcpy.result_program c).trans (called_program _ _ _)
  · exact (Memcpy.result_frame c .ERR trivial).trans ((called_error _ _ _).trans error)
  · intro reg untouched
    have h1 : reg ≠ 1#5 := by simp_all
    have h2 : reg ≠ 2#5 := by simp_all
    have h3 : reg ≠ 3#5 := by simp_all
    have h4 : reg ≠ 4#5 := by simp_all
    have h30 : reg ≠ 30#5 := by simp_all
    exact (Memcpy.result_frame c (.GPR reg) ⟨h1, h2, h3, h4⟩).trans
      (called_register _ _ _ _ h30)
  · intro reg nonzero
    have preserved := Memcpy.result_frame c (.SFP reg) nonzero
    simpa [c, called, state_simp_rules] using preserved
  · intro offset bytes within
    have observed := BitVector.memcpy_observe c offset bytes dst src sep (by rwa [r2])
    simpa [r0, r1, c, widthLoad, called, state_simp_rules] using observed
  · have frame := BitVector.memcpy_frame c dst src sep
    simpa [r0, r2, Delimited.MemoryFrame, c, called, state_simp_rules] using frame

end SszArm.Measure.Helpers
