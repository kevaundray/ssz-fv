import SszArm.MeasureBitsAllocGeometry

namespace SszArm.Measure.Bits.Alloc

open UintCodec (widthLoad)

macro "measure_alloc_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

theorem commit_words (site : Site) (s : ArmState) (base : BitVec 64)
    (space : CommitSpace site s) :
    SszNative.NatMemory.wordsAt (widthLoad (commitResult site s base))
      (allocatedPointer site s).toNat [r (.GPR site.lowReg) s, r (.GPR site.highReg) s] := by
  have physical := space.payload
  intro index
  have positions : index.val = 0 ∨ index.val = 1 := by
    have bound := index.isLt
    simp only [List.length_cons, List.length_nil] at bound
    omega
  rcases positions with position | position
  all_goals
    simp only [widthLoad, position, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
      BitVec.ofNat_add, BitVec.ofNat_toNat]
    simp (config := {decide := true, instances := true}) (disch := measure_alloc_side)
      [commitResult, committedMemory, state_simp_rules, BitVec.add_assoc,
        UintCodec.Tail.write_pair_words, BoolCodec.read_mem_bytes_write_mem_bytes_same,
        BoolCodec.read_mem_bytes_write_mem_bytes_disjoint, position]

theorem commit_at (site : Site) (s : ArmState) (base : BitVec 64)
    (space : CommitSpace site s) :
    (SszNative.NatOperand.large (allocatedPointer site s)
      [r (.GPR site.lowReg) s, r (.GPR site.highReg) s]).At
        (widthLoad (commitResult site s base)) :=
  ⟨space.positive, space.aligned, by simpa using space.payload, commit_words site s base space⟩

theorem commit_cursor (site : Site) (s : ArmState) (base : BitVec 64)
    (space : CommitSpace site s) :
    read_mem_bytes 8 (r (.GPR 20#5) s + 16#64) (commitResult site s base) =
      r (.GPR site.workReg) s := by
  obtain ⟨header, positive, aligned, payload, separate⟩ := space
  simp (config := {decide := true, instances := true}) (disch := measure_alloc_side)
    [commitResult, committedMemory, state_simp_rules,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem commit_header (site : Site) (s : ArmState) (base : BitVec 64)
    (space : CommitSpace site s) :
    read_mem_bytes 8 (r (.GPR 20#5) s) (commitResult site s base) = addressWord s ∧
    read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) (commitResult site s base) = capacityWord s := by
  obtain ⟨header, positive, aligned, payload, separate⟩ := space
  constructor <;>
    simp (config := {decide := true, instances := true}) (disch := measure_alloc_side)
      [commitResult, committedMemory, addressWord, capacityWord, state_simp_rules,
        BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem commit_pair (site : Site) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.pointerReg) (commitResult site s base) = allocatedPointer site s ∧
    r (.GPR site.countReg) (commitResult site s base) = 2#64 := by
  cases site <;>
    simp [commitResult, committedMemory, Site.pointerReg, Site.countReg, state_simp_rules]

end SszArm.Measure.Bits.Alloc
