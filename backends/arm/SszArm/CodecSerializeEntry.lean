import SszArm.SerializeEntry
import SszArm.CodecStorageTypes
import SszArm.CodecStack

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (MemoryFrame)

/-- Both recursive callees reuse the same caller activation. Their stack
requirements are combined by maximum, including each callee's lowerings. -/
def stackBytes (measurement emission : Nat) : Nat := 144 + max measurement emission

theorem measure_stack_low {sp measurement emission : Nat}
    (enough : stackBytes measurement emission ≤ sp) : measurement ≤ sp - 144 := by
  have child := Nat.le_max_left measurement emission
  unfold stackBytes at enough
  omega

theorem emit_stack_low {sp measurement emission : Nat}
    (enough : stackBytes measurement emission ≤ sp) : emission ≤ sp - 144 := by
  have child := Nat.le_max_right measurement emission
  unfold stackBytes at enough
  omega

/-- Actual original wrapper entry through its first BL. Recursive immutable
storage is preserved as a whole, including shared descriptor/value backings.
The coverage hypothesis is solely original-state interval geometry. -/
theorem entry_correct (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (writes : List Delimited.Span)
    (code : SszArm.Serialize.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (stack : 432 ≤ (r (.GPR 31#5) s).toNat)
    (cover : BitVector.Covers writes (SszArm.Serialize.saveWrites (SszArm.Serialize.Args.ofEntry s)))
    (descriptor : Storage.DescOwned writes s (r (.GPR 1#5) s).toNat desc)
    (input : Storage.ValueOwned writes s (r (.GPR 2#5) s).toNat value) :
    run 13 s = SszArm.Serialize.measurementEntry base s ∧
      Storage.DescOwned writes (SszArm.Serialize.measurementEntry base s)
        (r (.GPR 1#5) s).toNat desc ∧
      Storage.ValueOwned writes (SszArm.Serialize.measurementEntry base s)
        (r (.GPR 2#5) s).toNat value ∧
      MemoryFrame writes s (SszArm.Serialize.measurementEntry base s) := by
  have frame := cover.frame (SszArm.Serialize.measurementEntry_frame s base stack)
  exact ⟨SszArm.Serialize.measurementEntry_run s base code error aligned pc,
    Storage.desc_preserved descriptor frame, Storage.value_preserved input frame, frame⟩

end SszArm.Codec.Serialize
