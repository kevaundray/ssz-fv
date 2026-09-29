import SszArm.IndicesGeneralizedIndexEmptyObservation
import SszIndicesPaths

namespace SszArm.Indices.GeneralizedIndex.Empty

theorem emptyMemory_pointer (s : ArmState) (owned : Owned s) :
    read_mem_bytes 8 (r (.GPR 0#5) s) (emptyMemory s) = 0#64 := by
  have apart := output_stack_apart s owned
  have low := owned.stackLow
  have bound := owned.outputBound
  have spBound := (r (.GPR 31#5) s).isLt
  have p8 := output_toNat s owned 8 (by decide)
  have p64 := output_toNat s owned 64 (by decide)
  simp (disch := (simp (disch := omega) only [stackSlot_toNat s owned, p8, p64]; omega)) only
    [emptyMemory, BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem emptyMemory_payload (s : ArmState) (owned : Owned s) :
    read_mem_bytes 8 (r (.GPR 0#5) s + 8#64) (emptyMemory s) = 1#64 := by
  have apart := output_stack_apart s owned
  have low := owned.stackLow
  have bound := owned.outputBound
  have spBound := (r (.GPR 31#5) s).isLt
  have p8 := output_toNat s owned 8 (by decide)
  have p64 := output_toNat s owned 64 (by decide)
  simp (disch := (simp (disch := omega) only [stackSlot_toNat s owned, p8, p64]; omega)) only
    [emptyMemory, BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem emptyMemory_status (s : ArmState) (owned : Owned s) :
    read_mem_bytes 4 (r (.GPR 0#5) s + 64#64) (emptyMemory s) = 0#32 := by
  have p64 := output_toNat s owned 64 (by decide)
  have bound := owned.outputBound
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ _ _ _ (by rw [p64]; omega)

theorem empty_result_words (s : ArmState) (owned : Owned s) :
    read_mem_bytes 8 (r (.GPR 0#5) s) (emptyReturned s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 0#5) s + 8#64) (emptyReturned s) = 1#64 ∧
    read_mem_bytes 4 (r (.GPR 0#5) s + 64#64) (emptyReturned s) = 0#32 := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (emptyReturned_memory s owned))]
  exact ⟨emptyMemory_pointer s owned, emptyMemory_payload s owned, emptyMemory_status s owned⟩

/-- Empty-path semantics neither reads the descriptor nor changes the arena.
This model equation is used only after the actual stored result is derived. -/
theorem empty_source (shape : SszNative.Codec.Desc) (base capacity used : Nat) :
    SszNative.Indices.generalizedIndex shape [] base capacity used =
      SszNative.Indices.unchanged used (.ok (.small 1)) := rfl

end SszArm.Indices.GeneralizedIndex.Empty
