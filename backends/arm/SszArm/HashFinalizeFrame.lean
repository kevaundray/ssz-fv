import SszArm.HashFinalizeGeometry
import SszArm.BoolAlignment
import SszArm.HashFinalizeScalar

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

/-- The physical save slots remain live until the original two restore instructions. -/
structure Saved (s t : ArmState) : Prop where
  link : read_mem_bytes 8 (bodySP s) t = r (.GPR 30#5) s
  pair : read_mem_bytes 16 (bodySP s + 16#64) t =
    r (.GPR 19#5) s ++ r (.GPR 20#5) s

/-- The local activation excludes caller-saved integer registers and NZCV. -/
structure Activation (s t : ArmState) : Prop where
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = bodySP s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
    reg ≠ 19#5 → reg ≠ 20#5 → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  saved : Saved s t
  frame : MemoryFrame (finalizeWrites s) s t

structure Live (s t : ArmState) : Prop extends Activation s t where
  output : r (.GPR 19#5) t = outputPtr s
  state : r (.GPR 20#5) t = statePtr s

theorem Saved.frame {s t u : ArmState} {writes : List Span}
    (saved : Saved s t) (g : Geometry s) (frame : MemoryFrame writes t u)
    (owned : Protected writes (bodySP s).toNat 32) : Saved s u := by
  have spNat := g.bodySP_nat
  have low := g.stackLow
  have topBound := (stackTop s).isLt
  have bound : (bodySP s).toNat + 32 ≤ 2^64 := by omega
  have at16 : (bodySP s + 16#64).toNat = (bodySP s).toNat + 16 := by bv_omega
  constructor
  · rw [read_frame _ 8 frame (by omega)
      (protected_subspan owned (Nat.le_refl _) (by omega))]
    exact saved.link
  · rw [read_frame _ 16 frame (by rw [at16]; omega)
      (by rw [at16]; exact protected_subspan owned (by omega) (by omega))]
    exact saved.pair

theorem Activation.code {s t : ArmState} {base : BitVec 64}
    (activation : Activation s t) (code : CodeAt s base) : CodeAt t base :=
  code.of_program_eq activation.program

theorem Activation.data {s t : ArmState} {base : BitVec 64} {value : StreamState}
    (activation : Activation s t) (data : DataAt s base)
    (owned : FinalizeOwned s base value) : DataAt t base :=
  data.frame activation.frame owned.initialOwned owned.roundsOwned

theorem Activation.aligned {s t : ArmState} (activation : Activation s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  have stack := BoolCodec.stack_aligned s aligned
  have lower := BoolCodec.aligned_sub32 _ stack
  change Aligned (bodySP s) 4 at lower
  exact CheckSPAlignment_of_r_sp_aligned activation.sp lower

theorem Activation.returned {s t u : ArmState} {writes : List Span}
    (activation : Activation s t) (g : Geometry s) (returned : Returned t u)
    (frame : MemoryFrame writes t u)
    (contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2)
    (savedOwned : Protected writes (bodySP s).toNat 32) : Activation s u := by
  refine ⟨returned.error, returned.program.trans activation.program,
    returned.sp.trans activation.sp, ?_, ?_, activation.saved.frame g frame savedOwned,
    activation.frame.trans (frame_mono frame contained)⟩
  · intro reg lo hi h19 h20
    exact (returned.registers reg lo (by omega)).trans
      (activation.registers reg lo hi h19 h20)
  · intro reg lo hi
    exact (returned.vectors reg lo hi).trans (activation.vectors reg lo hi)

theorem Live.returned {s t u : ArmState} {writes : List Span}
    (live : Live s t) (g : Geometry s) (returned : Returned t u)
    (frame : MemoryFrame writes t u)
    (contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2)
    (savedOwned : Protected writes (bodySP s).toNat 32) : Live s u := by
  refine ⟨live.toActivation.returned g returned frame contained savedOwned, ?_, ?_⟩
  · exact (returned.registers 19#5 (by decide) (by decide)).trans live.output
  · exact (returned.registers 20#5 (by decide) (by decide)).trans live.state

theorem Activation.advance {s t u : ArmState} {writes : List Span}
    {changed : List (BitVec 5)} (activation : Activation s t) (g : Geometry s)
    (scalar : ScalarFrame changed t u)
    (kept : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
      reg ≠ 19#5 → reg ≠ 20#5 → reg ∉ changed)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) t)
    (frame : MemoryFrame writes t u)
    (contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2)
    (savedOwned : Protected writes (bodySP s).toNat 32) : Activation s u := by
  refine ⟨scalar.error.trans activation.error, scalar.program.trans activation.program,
    sp.trans activation.sp, ?_, ?_, activation.saved.frame g frame savedOwned,
    activation.frame.trans (frame_mono frame contained)⟩
  · intro reg lo hi h19 h20
    exact (scalar.registers reg (kept reg lo hi h19 h20)).trans
      (activation.registers reg lo hi h19 h20)
  · intro reg lo hi
    rw [scalar.vectors]
    exact activation.vectors reg lo hi

theorem Live.advance {s t u : ArmState} {writes : List Span}
    {changed : List (BitVec 5)} (live : Live s t) (g : Geometry s)
    (scalar : ScalarFrame changed t u)
    (kept : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 → reg ∉ changed)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) t)
    (frame : MemoryFrame writes t u)
    (contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2)
    (savedOwned : Protected writes (bodySP s).toNat 32) : Live s u := by
  refine ⟨live.toActivation.advance g scalar (fun reg lo hi _ _ => kept reg lo hi)
    sp frame contained savedOwned, ?_, ?_⟩
  · exact (scalar.registers 19#5 (kept _ (by decide) (by decide))).trans live.output
  · exact (scalar.registers 20#5 (kept _ (by decide) (by decide))).trans live.state

theorem Activation.sameMemory {s t u : ArmState} {changed : List (BitVec 5)}
    (activation : Activation s t) (g : Geometry s) (scalar : ScalarFrame changed t u)
    (kept : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
      reg ≠ 19#5 → reg ≠ 20#5 → reg ∉ changed)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) t) (memory : u.mem = t.mem) :
    Activation s u := by
  apply activation.advance g scalar kept sp
    (writes := []) (fun _ _ => congrFun memory _)
  · simp
  · right; simp

theorem Live.sameMemory {s t u : ArmState} {changed : List (BitVec 5)}
    (live : Live s t) (g : Geometry s) (scalar : ScalarFrame changed t u)
    (kept : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 → reg ∉ changed)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) t) (memory : u.mem = t.mem) :
    Live s u := by
  apply live.advance g scalar kept sp (writes := []) (fun _ _ => congrFun memory _)
  · simp
  · right; simp

end SszArm.Hash.Finalize
