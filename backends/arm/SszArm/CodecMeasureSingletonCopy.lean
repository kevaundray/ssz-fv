import SszArm.CodecMeasurePlanCopy
import SszArm.CodecLinked
import SszArm.CodecLinkedBranches
import SszArm.BitVectorMemcpy

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

def copyCalled (s : ArmState) (bias : BitVec 64) : ArmState :=
  w (.GPR 30#5) (bias + 2299980#64) (w .PC (bias + 2413776#64) s)

@[simp] theorem copyCalled_program (s : ArmState) (bias : BitVec 64) :
    (copyCalled s bias).program = s.program := by simp [copyCalled, state_simp_rules]

@[simp] theorem copyCalled_error (s : ArmState) (bias : BitVec 64) :
    read_err (copyCalled s bias) = read_err s := by simp [copyCalled, state_simp_rules]

theorem copyCalled_register (s : ArmState) (bias : BitVec 64) (reg : BitVec 5)
    (notLink : reg ≠ 30#5) : r (.GPR reg) (copyCalled s bias) = r (.GPR reg) s := by
  simp [copyCalled, state_simp_rules, notLink]

theorem copy_call_step (s : ArmState) (bias : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s (bias + 2299872#64))
    (error : read_err s = .None) (pc : read_pc s = bias + 2299976#64) :
    stepi s = copyCalled s bias := by
  apply Linked.Branches.plan_singleton_p104 s bias error pc
  simpa only [BitVec.add_assoc, show 2299872#64 + 104#64 = 2299976#64 by decide]
    using Linked.PlanSingleton.chunk0_codeAt code (104, 0x94006f22#32) (by decide)

theorem copy_run (s : ArmState) (bias : BitVec 64)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (pc : read_pc s = bias + 2299976#64) :
    run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s = Memcpy.result (copyCalled s bias) := by
  rw [run, copy_call_step s bias code.plan_singleton error pc]
  have runtime : SszArm.CodeAt (copyCalled s bias) (bias + 2413776#64) Memcpy.program := by
    simpa only [SszArm.CodeAt, copyCalled_program] using code.memcpy
  have count := copyCalled_register s bias 2#5 (by decide)
  rw [← count]
  exact Memcpy.program_run _ _ runtime (by simp [copyCalled, state_simp_rules])
    ((copyCalled_error s bias).trans error)

structure CopyPost (s t : ArmState) (bias : BitVec 64) : Prop where
  pc : read_pc t = bias + 2299980#64
  program : t.program = s.program
  error : read_err t = .None
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  copied : ∀ offset bytes, offset + bytes ≤ (r (.GPR 2#5) s).toNat →
    widthLoad t ((r (.GPR 0#5) s).toNat + offset) bytes =
      widthLoad s ((r (.GPR 1#5) s).toNat + offset) bytes
  frame : MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s t

theorem copy_correct (s : ArmState) (bias : BitVec 64)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (pc : read_pc s = bias + 2299976#64)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat) :
    CopyPost s (run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s) bias := by
  rw [copy_run s bias code error pc]
  let c := copyCalled s bias
  have r0 : r (.GPR 0#5) c = r (.GPR 0#5) s := copyCalled_register _ _ _ (by decide)
  have r1 : r (.GPR 1#5) c = r (.GPR 1#5) s := copyCalled_register _ _ _ (by decide)
  have r2 : r (.GPR 2#5) c = r (.GPR 2#5) s := copyCalled_register _ _ _ (by decide)
  have dst : (r (.GPR 0#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r0, r2]
  have src : (r (.GPR 1#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by rwa [r1, r2]
  have sep : Memcpy.Disjoint (r (.GPR 0#5) c) (r (.GPR 1#5) c) (r (.GPR 2#5) c).toNat := by
    rwa [r0, r1, r2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c, copyCalled, state_simp_rules] using Memcpy.result_return c
  · exact (Memcpy.result_program c).trans (copyCalled_program s bias)
  · exact (Memcpy.result_frame c .ERR trivial).trans ((copyCalled_error s bias).trans error)
  · intro reg untouched
    have h1 : reg ≠ 1#5 := by simp_all
    have h2 : reg ≠ 2#5 := by simp_all
    have h3 : reg ≠ 3#5 := by simp_all
    have h4 : reg ≠ 4#5 := by simp_all
    have h30 : reg ≠ 30#5 := by simp_all
    exact (Memcpy.result_frame c (.GPR reg) ⟨h1, h2, h3, h4⟩).trans
      (copyCalled_register _ _ _ h30)
  · intro reg nonzero
    simpa [c, copyCalled, state_simp_rules] using Memcpy.result_frame c (.SFP reg) nonzero
  · intro offset bytes within
    have observed := BitVector.memcpy_observe c offset bytes dst src sep (by rwa [r2])
    simpa [r0, r1, c, widthLoad, copyCalled, state_simp_rules] using observed
  · have frame := BitVector.memcpy_frame c dst src sep
    simpa [r0, r2, Delimited.MemoryFrame, c, copyCalled, state_simp_rules] using frame

theorem CopyPost.plan {s t : ArmState} {bias : BitVec 64} (post : CopyPost s t bias)
    (plan : SszNative.CodecMeasure.Plan) (count : r (.GPR 2#5) s = 40#64)
    (physical : Storage.Physical (r (.GPR 0#5) s).toNat 40 8)
    (owned : Storage.PlanOwned [((r (.GPR 0#5) s).toNat, 40)] s
      (r (.GPR 1#5) s).toNat plan) :
    Storage.PlanAt t (r (.GPR 0#5) s).toNat plan := by
  have frame : MemoryFrame [((r (.GPR 0#5) s).toNat, 40)] s t := by
    simpa only [count, BitVec.toNat_ofNat] using post.frame
  have preserved := Storage.plan_at (Storage.plan_preserved owned frame)
  apply plan_copy plan preserved physical
  intro offset bytes within
  have copied := post.copied offset bytes (by simpa only [count, BitVec.toNat_ofNat] using within)
  have root : Delimited.Protected [((r (.GPR 0#5) s).toNat, 40)]
      (r (.GPR 1#5) s).toNat 40 := by
    cases plan
    exact owned.1.2
  have sourceBound : (r (.GPR 1#5) s).toNat + 40 ≤ 2^64 := by
    cases plan
    exact owned.1.1.2.2.1
  have localProtected := root.subspan offset bytes within
  rw [frame.load ((r (.GPR 1#5) s).toNat + offset) bytes
    (by omega) localProtected]
  exact copied

end SszArm.Codec.Measure.Singleton
