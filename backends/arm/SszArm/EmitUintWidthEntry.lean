import SszArm.EmitUintWidthExec
import SszArm.EmitUintFrame

namespace SszArm.Emit.Uint

def widthReadonlyOps : List WidthOp :=
  [.p60, .p64, .p68, .p72, .p76, .p80, .p84, .p96, .p100, .p104, .p108,
   .p120, .p124, .p128, .p132, .p136, .p140, .p896, .p900, .p904, .p908, .p912]

theorem width_readonly_frame (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (args : Args) (size : Nat) (hops : ∀ op ∈ ops, op ∈ widthReadonlyOps) :
    Frame s (widthBlock base ops s) args size := by
  induction ops generalizing s with
  | nil => exact Frame.refl s args size
  | cons op ops ih =>
    have member := hops op List.mem_cons_self
    have hf : Frame s (op.effect base s) args size := by
      cases op <;> simp_all only [widthReadonlyOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact WidthOp.program _ _ _
        · exact WidthOp.error _ _ _
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [WidthOp.effect, put, next, Dispatch.next,
            Dispatch.compare64, Dispatch.compare32, state_simp_rules]
        · intro reg; exact WidthOp.vector _ _ _ _
        · intro a ha
          simp [WidthOp.effect, put, next, Dispatch.next,
            Dispatch.compare64, Dispatch.compare32, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hops op (List.mem_cons_of_mem _ hop)))

def headerOps : List WidthOp := [.p60, .p64, .p68, .p72]

@[irreducible] def widthHeader (base : BitVec 64) (s : ArmState) : ArmState :=
  widthBlock base headerOps s

theorem header_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 60#64) (tag : r (.GPR 9#5) s = 1#64) :
    run 4 s = widthHeader base s := by
  rw [widthHeader]
  apply width_run base headerOps s code error aligned
  change r .PC s = base + 60#64 at pc
  simp (config := {decide := true, instances := true})
    [headerOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Dispatch.next,
     Dispatch.compare32, state_simp_rules, bitvec_rules, minimal_theory, pc, tag,
     BitVec.add_assoc]

theorem header_frame (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) :
    Frame s (widthHeader base s) args size := by
  rw [widthHeader]
  exact width_readonly_frame base headerOps s args size (by decide)

theorem header_pair (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : SszNative.NatOperand) (size : Nat)
    (owned : Owned s args (.uint width) (.uint number) size)
    (descriptor : r (.GPR 1#5) s = args.descriptor) :
    r (.GPR 8#5) (widthHeader base s) = width.pointer ∧
    r (.GPR 1#5) (widthHeader base s) = width.payload := by
  have pair := descriptor_pair owned
  simpa [widthHeader, headerOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
    Dispatch.compare32, state_simp_rules, descriptor] using pair

theorem header_pc (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : SszNative.NatOperand) (size : Nat)
    (owned : Owned s args (.uint width) (.uint number) size)
    (descriptor : r (.GPR 1#5) s = args.descriptor) :
    read_pc (widthHeader base s) = base +
      (if width.pointer = 0#64 then 904#64 else 76#64) := by
  have pair := descriptor_pair owned
  simp [widthHeader, headerOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
    Dispatch.compare32, state_simp_rules, descriptor, pair.1, apply_ite]

end SszArm.Emit.Uint
