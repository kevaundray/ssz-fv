import SszArm.NatDivisionExhausted

namespace SszArm.NatDivision

open Delimited (MemoryFrame Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Even the size-overflow and alignment-spill failure paths execute to the
complete error result and original RET, without committing the arena cursor. -/
theorem large_exhausted_post (original s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 168#64) (positive : 0 < (r (.GPR 8#5) s).toNat)
    (failed : (outcome original operand).result = .error .scratchExhausted)
    (reserve : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used (r (.GPR 8#5) s).toNat = none)
    (before : MemoryFrame (localWrites original) original s) :
    ∃ fuel, Post original (run fuel s) operand := by
  let address := read_mem_bytes 8 (r (.GPR 4#5) original) original
  let capacity := read_mem_bytes 8 (r (.GPR 4#5) original + 8#64) original
  let used := read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) original
  have hbase : read_mem_bytes 8 (r (.GPR 21#5) s) s = address := by
    simpa [address] using local_arena_word owned before arena 0 (by decide)
  have hcapacity : read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s = capacity := by
    simpa [capacity] using local_arena_word owned before arena 8 (by decide)
  have hused : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = used := by
    simpa [used] using local_arena_word owned before arena 16 (by decide)
  have reserve' : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (r (.GPR 8#5) s).toNat = none := reserve
  have stack := owned.stackBound
  have headerBound := owned.arenaBound
  have slot : (r (.GPR 31#5) s).toNat - 16 = (r (.GPR 31#5) original).toNat - 80 := by
    rw [saved.sp]
    bv_omega
  have physical : ∀ offset ∈ [0#64, 8#64, 16#64],
      (r (.GPR 21#5) s + offset).toNat + 8 ≤ 2^64 := by
    intro offset member
    rw [arena]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> bv_omega
  have apart : (r (.GPR 4#5) original).toNat + 24 ≤ (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ (r (.GPR 4#5) original).toNat := by
    rcases owned.arenaLocal with empty | separate
    · omega
    · have h := separate ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at h
      omega
  have headerOwned : ∀ offset ∈ [0#64, 8#64, 16#64],
      Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
        (r (.GPR 21#5) s + offset).toNat 8 := by
    intro offset member
    right
    intro span present
    simp only [List.mem_singleton] at present
    subst span
    rw [arena, slot]
    simp only [Prod.fst, Prod.snd, List.mem_cons, List.not_mem_nil, or_false] at *
    rcases member with rfl | rfl | rfl <;> bv_omega
  have unchanged := SszNative.NatDivision.failure_unchanged operand (r (.GPR 3#5) original)
    (arenaOf original).base (arenaOf original).capacity (arenaOf original).used .scratchExhausted failed
  have unallocated : (outcome original operand).allocation = none := by rw [unchanged]; rfl
  have finish (t : ArmState) (frame : ArenaFrame s t)
      (memory : MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t)
      (pc : read_pc t = base + 812#64) : Post original (run 54 t) operand := by
    have body : MemoryFrame (bodyWrites original operand) s t := by
      apply memory.weaken
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp [bodyWrites, unallocated, slot]
    have local : MemoryFrame (localWrites original) s t := by
      simpa only [writesFor, unallocated] using body_frame_full operand body
    exact failure_post original t base operand owned (frame.saved_body owned body saved)
      ((frame.registers 19#5 (by decide)).trans out) (frame.code base hc)
      (frame.error.trans he) (frame.aligned ha) pc failed (before.trans local)
  obtain ⟨fuel, t, executed, post⟩ := arena_big_reservation_runs s base address capacity used
    hc he ha hp (by rw [saved.sp]; bv_omega) positive hbase hcapacity hused physical headerOwned
  refine ⟨fuel + 54, ?_⟩
  rw [run_plus, executed]
  rcases post with early | ⟨u, frame, memory, later, count⟩
  · exact finish t early.2.2.1 early.2.2.2 early.2.1
  · rcases later with late | committed
    · have extra : MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] u t := by
        intro a _
        exact congrArg (fun bytes => bytes a) late.2.2.memory
      exact finish t (frame.trans late.2.2.frame) (memory.trans extra) late.2.1
    · have impossible := committed.1
      rw [reserve'] at impossible
      cases impossible

end SszArm.NatDivision
