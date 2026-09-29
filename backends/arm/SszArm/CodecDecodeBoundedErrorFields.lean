import SszArm.CodecDecodeBoundedErrorMemory

namespace SszArm.Codec.Decode.Bounded

/-- Geometry of the real sixteen-byte lowering scratch and the meaningful
sixty-eight-byte error record. It does not constrain borrowed input aliases. -/
structure ErrorSpace (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 19#5) s).toNat + 68 ≤ 2 ^ 64
  apart : (r (.GPR 19#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 19#5) s).toNat

macro "bounded_error_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

macro "bounded_error_reads" : tactic => `(tactic|
  simp (disch := bounded_error_side) only
    [BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_eq_ofNat,
     BitVec.add_zero, BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint])

theorem tag_fields (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    read_mem_bytes 8 (r (.GPR 19#5) s) (ErrorStage.tag.result s base) = r (.GPR 8#5) s ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) (ErrorStage.tag.result s base) = 0#64 := by
  obtain ⟨stack, output, apart⟩ := space
  simp only [Memory.mem_eq_iff_read_mem_bytes_eq.mp (error_stage_memory .tag s base),
    ErrorStage.memory]
  constructor <;> bounded_error_reads

theorem actual_fields (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    read_mem_bytes 8 (r (.GPR 19#5) s + 32#64) (ErrorStage.actual.result s base) =
      read_mem_bytes 8 (r (.GPR 20#5) s) s ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 40#64) (ErrorStage.actual.result s base) =
      read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) s ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 48#64) (ErrorStage.actual.result s base) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 56#64) (ErrorStage.actual.result s base) = 0#64 ∧
    read_mem_bytes 4 (r (.GPR 19#5) s + 64#64) (ErrorStage.actual.result s base) = 2#32 := by
  obtain ⟨stack, output, apart⟩ := space
  simp only [Memory.mem_eq_iff_read_mem_bytes_eq.mp (error_stage_memory .actual s base),
    ErrorStage.memory, UintCodec.Tail.write_pair_words]
  repeat' constructor
  all_goals bounded_error_reads

/-- The later actual-operand stage leaves the tag and expected operand in
place. Only meaningful initialized fields are transported. -/
theorem actual_preserves_prefix (s : ArmState) (base : BitVec 64) (space : ErrorSpace s)
    (offset width : Nat) (prefix : offset + width ≤ 32) :
    read_mem_bytes width (r (.GPR 19#5) s + BitVec.ofNat 64 offset)
      (ErrorStage.actual.result s base) =
    read_mem_bytes width (r (.GPR 19#5) s + BitVec.ofNat 64 offset) s := by
  obtain ⟨stack, output, apart⟩ := space
  simp only [Memory.mem_eq_iff_read_mem_bytes_eq.mp (error_stage_memory .actual s base),
    ErrorStage.memory]
  bounded_error_reads

/-- The tag lowering does not overwrite the expected operand record. -/
theorem tag_preserves_expected (s : ArmState) (base : BitVec 64) (space : ErrorSpace s)
    (offset width : Nat) (low : 16 ≤ offset) (high : offset + width ≤ 32) :
    read_mem_bytes width (r (.GPR 19#5) s + BitVec.ofNat 64 offset)
      (ErrorStage.tag.result s base) =
    read_mem_bytes width (r (.GPR 19#5) s + BitVec.ofNat 64 offset) s := by
  obtain ⟨stack, output, apart⟩ := space
  simp only [Memory.mem_eq_iff_read_mem_bytes_eq.mp (error_stage_memory .tag s base),
    ErrorStage.memory]
  bounded_error_reads

end SszArm.Codec.Decode.Bounded
