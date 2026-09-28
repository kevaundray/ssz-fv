import SszArm.MeasureBitsListPrefix

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (Protected MemoryFrame)

theorem Prefix.lower_step {schema : Schema} {s u t : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits)) (pre : Prefix s u args schema bits actual)
    (core : Core t args schema bits actual) (program : t.program = u.program)
    (error : read_err t = read_err u)
    (frame : MemoryFrame (Helpers.loweringWrites u) u t)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] → r (.GPR reg) t = r (.GPR reg) u)
    (vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) u) : Prefix s t args schema bits actual := by
  have headerOwned : Protected (Helpers.loweringWrites u) args.arena.toNat 24 := by
    rcases owned.headerLocal with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      exact separate span (lowering_subset_local args _ u owned.stackLow pre.core.stack span member)
  have free : Protected (Helpers.loweringWrites u)
      ((arenaOf s args).base + (arenaOf s args).used)
      ((arenaOf s args).capacity - (arenaOf s args).used) := by
    rcases owned.freeLocal with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      exact separate span (List.mem_append.mpr (Or.inl
        (lowering_subset_local args _ u owned.stackLow pre.core.stack span member)))
  have r0 := Emit.frame_read_offset frame args.arena 24 0 8 owned.arenaBound headerOwned (by decide)
  have r8 := Emit.frame_read_offset frame args.arena 24 8 8 owned.arenaBound headerOwned (by decide)
  have r16 := Emit.frame_read_offset frame args.arena 24 16 8 owned.arenaBound headerOwned (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨pre.counted, program.trans pre.program, error.trans pre.error, core,
    NatDivision.operand_at_preserved frame actual pre.actualAt (Prefix.actual_lower_owned owned pre),
    ?_, ⟨r0.trans pre.header.1, r8.trans pre.header.2⟩,
    Helpers.fromWide_written_preserved (arenaOf s args) bits.count owned.storageBound free frame pre.written,
    ?_, ?_, ?_⟩
  · rw [r16]
    exact pre.cursor
  · apply pre.frame.trans (frame.weaken ?_)
    intro span member
    have position : (r (.GPR 31#5) u).toNat - 16 = args.stack.toNat - 288 := by
      have low := owned.stackLow
      rw [pre.core.stack, Args.bodySP]
      bv_omega
    simp only [Helpers.loweringWrites, position, List.mem_singleton] at member
    subst span
    exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  · intro reg member
    exact (registers reg member).trans (pre.registers reg member)
  · intro reg
    exact (vectors reg).trans (pre.vectors reg)

end SszArm.Measure.Bits.List
