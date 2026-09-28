import SszArm.BitVectorStageState
import SszArm.BitVectorResources

namespace SszArm.BitVector

/-- Arena observations are relative to the original descriptor even after W19
has been repurposed for the rounding status. -/
structure ArenaAt (s t : ArmState) (used : Nat) : Prop where
  base : read_mem_bytes 8 (r (.GPR 19#5) s) t = read_mem_bytes 8 (r (.GPR 19#5) s) s
  capacity : read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s
  cursor : (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) t).toNat = used

theorem local_arena_word {s a b : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (frame : Delimited.MemoryFrame (localWrites s) a b)
    (offset : Nat) (within : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 19#5) s + BitVec.ofNat 64 offset) b =
      read_mem_bytes 8 (r (.GPR 19#5) s + BitVec.ofNat 64 offset) a := by
  have bound := owned.arenaBound
  have address : (r (.GPR 19#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 19#5) s).toNat + offset := by bv_omega
  apply frame.read _ 8 (by rw [address]; omega)
  rw [address]
  exact owned.arenaLocal.subspan offset 8 within

theorem ArenaAt.after_local {s a b : ArmState} {length : SszNative.NatOperand}
    {data : Ssz.Bytes} {used : Nat} (current : ArenaAt s a used)
    (owned : Owned s length data) (frame : Delimited.MemoryFrame (localWrites s) a b) :
    ArenaAt s b used := by
  refine ⟨?_, ?_, ?_⟩
  · have same := local_arena_word owned frame 0 (by decide)
    simp only [BitVec.add_zero] at same
    exact same.trans current.base
  · exact (local_arena_word owned frame 8 (by decide)).trans current.capacity
  · have same : read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) b =
        read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) a :=
      local_arena_word owned frame 16 (by decide)
    exact (congrArg BitVec.toNat same).trans current.cursor

theorem division_arena {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {data : Ssz.Bytes} (owned : Owned s length data)
    (post : NatDivision.Post (divisionEntry s base) d length) :
    ArenaAt s d (outcome s length data).divided.used := by
  have args := division_arguments s base length data owned
  refine ⟨?_, ?_, ?_⟩
  · have preserved := post.arena.base
    rw [args.arena] at preserved
    simpa only [Memory.State.read_mem_bytes_eq_mem_read_bytes, args.memory] using preserved
  · have preserved := post.arena.capacity
    rw [args.arena] at preserved
    simpa only [Memory.State.read_mem_bytes_eq_mem_read_bytes, args.memory] using preserved
  · have used := post.cursor
    rw [args.arena, division_outcome s base length data owned] at used
    exact used

theorem division_arena_register {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} (post : NatDivision.Post (divisionEntry s base) d length) :
    r (.GPR 19#5) (Block.divisionStatusResult d base) = r (.GPR 19#5) s := by
  have kept := post.returned.registers 19#5 (by decide) (by decide)
  simpa (config := {decide := true}) [Block.divisionStatusResult, divisionEntry,
    called, Entry.result, state_simp_rules] using kept

theorem division_private_register {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} (post : NatDivision.Post (divisionEntry s base) d length) :
    r (.GPR 27#5) (Block.divisionStatusResult d base) = r (.GPR 31#5) s + 144#64 := by
  have kept := post.returned.registers 27#5 (by decide) (by decide)
  simpa (config := {decide := true}) [Block.divisionStatusResult, divisionEntry,
    called, Entry.result, state_simp_rules] using kept

end SszArm.BitVector
