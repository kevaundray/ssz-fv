import SszArm.IndicesElementTypeOwned
import SszArm.IndicesElementTypeBooleanMemory
import SszIndicesDescriptor

set_option autoImplicit false

namespace SszArm.Indices.ElementType

open SszNative.Codec (Desc)
open SszNative.Indices (PathStep)

/-- The full element_type activation uses a 16-byte save plus one 16-byte
lowering slot. All result writes lie in the 68-byte active Result extent. -/
def writes (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 0#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 32, 32)]

structure Owned (s : ArmState) (shape : Desc) (step : PathStep) : Prop where
  stackLow : 32 ≤ (r (.GPR 31#5) s).toNat
  output : Codec.Storage.Physical (r (.GPR 0#5) s).toNat 68 8
  outputStack : (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 32 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  descriptor : Codec.Storage.DescOwned (writes s) s (r (.GPR 1#5) s).toNat shape
  path : (Storage.pathStep (r (.GPR 2#5) s).toNat step).Owned (writes s) s

private theorem entry_protected {s : ArmState} {address bytes : Nat}
    (low : 32 ≤ (r (.GPR 31#5) s).toNat)
    (protected : Delimited.Protected (writes s) address bytes) :
    Delimited.Protected (entryWrites s) address bytes := by
  rcases protected with empty | protected
  · exact Or.inl empty
  · right
    intro span member
    simp only [entryWrites, List.mem_singleton] at member
    subst span
    have apart := protected ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [writes])
    simp only [Prod.fst, Prod.snd] at apart ⊢
    omega

theorem Owned.entry {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : Owned s shape step) : EntryOwned s shape step := by
  refine ⟨by have low := owned.stackLow; omega, ?_, ?_⟩
  · exact Codec.Storage.Image.weaken _ (fun _ _ => entry_protected owned.stackLow)
      owned.descriptor
  · exact Codec.Storage.Image.weaken _ (fun _ _ => entry_protected owned.stackLow)
      owned.path

/-- The generic result contract retains original raw error operands and only
observes the active descriptor fields. The frame is the real AAPCS64 frame. -/
structure Result (s t : ArmState) (shape : Desc) (step : PathStep) : Prop where
  returned : Delimited.Returned s t
  value : (Storage.descResult (r (.GPR 0#5) s).toNat
    (SszNative.Indices.elementType shape step)).At t
  frame : Delimited.MemoryFrame (writes s) s t
  program : t.program = s.program

end SszArm.Indices.ElementType
