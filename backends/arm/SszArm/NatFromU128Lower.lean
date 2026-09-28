import SszArm.NatFromU128LowerEffects

namespace SszArm.NatFromU128

open Delimited (Span MemoryFrame)

/-- The lowering sequence has one compact memory-only effect; saved registers
are restored from the original physical scratch slot, not assumed restored. -/
theorem lower_effect (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (space : Space s) :
    block base kind.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * kind.ops.length)) (lowerMemory kind s) := by
  cases kind
  · exact lower_smallPair_effect s base space
  · exact lower_smallStatus_effect s base space
  · exact lower_wideStatus_effect s base space
  · exact lower_zero48_effect s base space
  · exact lower_zero32_effect s base space
  · exact lower_zero16_effect s base space
  · exact lower_errorPair_effect s base space

theorem lower_run (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    run kind.ops.length s = block base kind.ops s := by
  apply block_run base kind.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.entry := hp
  cases kind <;>
    simp [LowerKind.ops, LowerKind.entry, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

theorem lower_registers (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (space : Space s) (reg : BitVec 5) :
    r (.GPR reg) (block base kind.ops s) = r (.GPR reg) s := by
  rw [lower_effect kind s base space]
  cases kind <;> simp [lowerMemory, lowerSaved, state_simp_rules]

theorem lower_memory (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (space : Space s) : (block base kind.ops s).mem = (lowerMemory kind s).mem := by
  rw [lower_effect kind s base space, ArmState.mem_w_eq_mem]

theorem lower_pc (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (space : Space s) :
    read_pc (block base kind.ops s) = read_pc s + BitVec.ofNat 64 (4 * kind.ops.length) := by
  rw [lower_effect kind s base space]
  simp [state_simp_rules]

theorem lower_space (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (space : Space s) : Space (block base kind.ops s) := by
  rcases space with ⟨stack, output, separate⟩
  have all : Space s := ⟨stack, output, separate⟩
  exact ⟨by simpa only [lower_registers kind s base all] using stack,
    by simpa only [lower_registers kind s base all] using output,
    by simpa only [lower_registers kind s base all] using separate⟩

def lowerWrites (kind : LowerKind) (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat + kind.offset, kind.bytes),
   ((r (.GPR 31#5) s).toNat - 16, 16)]

theorem lower_frame (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (space : Space s) : MemoryFrame (lowerWrites kind s) s (block base kind.ops s) := by
  rw [Delimited.MemoryFrame]
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat + kind.offset, kind.bytes)
    (by simp [lowerWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [lowerWrites])
  rw [lower_memory kind s base space]
  obtain ⟨stack, output, separate⟩ := space
  cases kind <;> simp only [LowerKind.offset, LowerKind.bytes] at out <;>
    simp (disch := from128_side) [lowerMemory, lowerSaved, LowerKind.offset,
      BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

end SszArm.NatFromU128
