import SszArm.IndicesElementTypeBooleanFacts
import SszArm.BoolResultMemory
import SszArm.IndicesStorage

set_option autoImplicit false

namespace SszArm.Indices.ElementType.BooleanBody

structure Geometry (s : ArmState) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  output : Codec.Storage.Physical (r (.GPR 0#5) s).toNat 68 8
  apart : (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat

theorem Geometry.scratch {s : ArmState} (geometry : Geometry s) :
    (r (.GPR 31#5) s - 16#64).toNat = (r (.GPR 31#5) s).toNat - 16 := by
  have bound := (r (.GPR 31#5) s).isLt
  have low := geometry.stackLow
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem Geometry.scratchNext {s : ArmState} (geometry : Geometry s) :
    (r (.GPR 31#5) s - 16#64 + 8#64).toNat = (r (.GPR 31#5) s).toNat - 8 := by
  have bound := (r (.GPR 31#5) s).isLt
  have low := geometry.stackLow
  simp only [BitVec.toNat_add, geometry.scratch, BitVec.toNat_ofNat]
  omega

theorem Geometry.reason {s : ArmState} (geometry : Geometry s) :
    (r (.GPR 0#5) s + 64#64).toNat = (r (.GPR 0#5) s).toNat + 64 := by
  have bound := geometry.output.2.2.1
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The bool branch writes only its active descriptor tag, success reason, and
its real scratch slots; it does not initialize unused descriptor payload bytes. -/
def writes (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 0#5) s).toNat, 8), ((r (.GPR 0#5) s).toNat + 64, 4),
   ((r (.GPR 31#5) s).toNat - 16, 16)]

theorem body_frame {s : ArmState} (geometry : Geometry s) :
    Delimited.MemoryFrame (writes s) s (block ops s) := by
  intro address outside
  have tagApart := outside ((r (.GPR 0#5) s).toNat, 8) (by simp [writes])
  have reasonApart := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [writes])
  have scratchApart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [writes])
  simp only [Prod.fst, Prod.snd] at tagApart reasonApart scratchApart
  have outputBound := geometry.output.2.2.1
  have stackBound := (r (.GPR 31#5) s).isLt
  have low := geometry.stackLow
  simp only [block, ops, List.foldl, Op.effect, next, put, state_simp_rules,
    BitVec.sub_add_cancel]
  simp (disch := (simp only [geometry.scratch, geometry.scratchNext, geometry.reason]; omega)) only
    [BoolCodec.write_mem_bytes_frame]

theorem body_tag {s : ArmState} (geometry : Geometry s) :
    read_mem_bytes 8 (r (.GPR 0#5) s) (block ops s) = 0#64 := by
  have outputBound := geometry.output.2.2.1
  have stackBound := (r (.GPR 31#5) s).isLt
  have low := geometry.stackLow
  have separate := geometry.apart
  simp only [block, ops, List.foldl, Op.effect, next, put, state_simp_rules,
    BitVec.sub_add_cancel]
  simp (disch := (simp only [geometry.scratch, geometry.scratchNext, geometry.reason]; omega)) only
    [BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem body_reason {s : ArmState} (geometry : Geometry s) :
    read_mem_bytes 4 (r (.GPR 0#5) s + 64#64) (block ops s) = 0#32 := by
  have outputBound := geometry.output.2.2.1
  simp only [block, ops, List.foldl, Op.effect, next, put, state_simp_rules,
    BitVec.sub_add_cancel]
  apply BoolCodec.read_mem_bytes_write_mem_bytes_same
  rw [geometry.reason]
  omega

/-- The active-field physical postcondition is the shared descriptor-result image. -/
theorem body_result {s : ArmState} (geometry : Geometry s) :
    (Storage.descResult (r (.GPR 0#5) s).toNat
      (.ok (.primitive .bool))).At (block ops s) := by
  have physical : Codec.Storage.Physical (r (.GPR 0#5) s).toNat 40 8 := by
    obtain ⟨positive, aligned, bound, _⟩ := geometry.output
    exact ⟨positive, aligned, by omega, by decide⟩
  refine ⟨⟨⟨physical, True.intro⟩, ?_, True.intro⟩, ?_⟩
  · refine ⟨by have bound := geometry.output.2.2.1; omega, True.intro, ?_⟩
    change some (read_mem_bytes 8 (BitVec.ofNat 64 (r (.GPR 0#5) s).toNat)
      (block ops s)).toNat = some 0
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, body_tag geometry,
      BitVec.toNat_ofNat]
  · refine ⟨by have bound := geometry.output.2.2.1; omega, True.intro, ?_⟩
    change some (read_mem_bytes 4 (BitVec.ofNat 64 ((r (.GPR 0#5) s).toNat + 64))
      (block ops s)).toNat = some 0
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      body_reason geometry, BitVec.toNat_ofNat]

end SszArm.Indices.ElementType.BooleanBody
