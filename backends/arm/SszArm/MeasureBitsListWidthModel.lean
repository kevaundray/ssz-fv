import SszArm.MeasureBitsListPrefix
import SszArm.MeasureBitsWidth
import SszArm.MeasureBitsConstructorContract

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

def widthArena (s : ArmState) (args : Args) (bits : Packed) : SszNative.Delimited.ArenaState :=
  { arenaOf s args with used := (countCall s args bits).used }

def widthCall (s : ArmState) (args : Args) (bits : Packed) : SszNative.NatArithmetic.Outcome NatOperand :=
  SszNative.NatArithmetic.fromWide (widthArena s args bits).base (widthArena s args bits).capacity
    (widthArena s args bits).used (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))

theorem width_model {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ()) :
    outcome s args schema.descriptor (.bits bits) =
      ⟨(widthCall s args bits).result.mapError SszNative.Serialize.Error.arithmetic,
        (widthCall s args bits).used, [countCall s args bits, widthCall s args bits]⟩ := by
  have counted : (SszNative.Serialize.fromWide (arenaOf s args) bits.count).result = .ok actual := by
    change (countCall s args bits).result.mapError _ = _
    simp only [pre.counted, Except.mapError]
  rw [list_outcome]
  have model := SszNative.Serialize.measureList_after_bound schema.cap actual bits (arenaOf s args) counted checked
  simpa only [widthCall, widthArena, countCall, SszNative.Serialize.fromWide, List.singleton_append] using model

theorem width_two_calls {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ()) :
    (outcome s args schema.descriptor (.bits bits)).calls.length = 2 := by
  rw [width_model pre checked]
  rfl

theorem width_arena {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits)) (pre : Prefix s u args schema bits actual)
    (base : BitVec 64) : NatDivision.arenaOf (Width.result u base) = widthArena s args bits := by
  have stackLow : 16 ≤ (r (.GPR 31#5) u).toNat := by
    have low := owned.stackLow
    rw [pre.core.stack, Args.bodySP]
    bv_omega
  have frame := Width.result_frame u base stackLow
  have headerOwned : Delimited.Protected (Helpers.loweringWrites u) args.arena.toNat 24 := by
    rcases owned.headerLocal with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      exact separate span (lowering_subset_local args _ u owned.stackLow pre.core.stack span member)
  have r0 := Emit.frame_read_offset frame args.arena 24 0 8 owned.arenaBound headerOwned (by decide)
  have r8 := Emit.frame_read_offset frame args.arena 24 8 8 owned.arenaBound headerOwned (by decide)
  have r16 := Emit.frame_read_offset frame args.arena 24 16 8 owned.arenaBound headerOwned (by decide)
  simp only [BitVec.add_zero] at r0
  simp only [NatDivision.arenaOf, (Width.result_arguments u base).2.2.1, pre.core.arena,
    r0, r8, r16, pre.header.1, pre.header.2, pre.cursor, widthArena, arenaOf]

theorem width_outcome {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits)) (pre : Prefix s u args schema bits actual)
    (base : BitVec 64) : NatFromU128.outcome (Width.result u base) = widthCall s args bits := by
  have arena := width_arena owned pre base
  have count := Width.result_count u base bits.count pre.core.low pre.core.high
  change SszNative.NatArithmetic.fromWide (NatDivision.arenaOf (Width.result u base)).base
    (NatDivision.arenaOf (Width.result u base)).capacity (NatDivision.arenaOf (Width.result u base)).used
    (NatFromU128.wide (Width.result u base)) = _
  rw [arena]
  simpa only [NatFromU128.wide, count, widthCall]

end SszArm.Measure.Bits.List
