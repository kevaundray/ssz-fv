import SszArm.NatDivisionFailurePost
import SszArm.NatDivisionArenaInput

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Every real count-two reservation guard is executed. On exhaustion the
cursor remains unmodified, and the complete error writer and RET are composed. -/
theorem wide_exhausted_post (original s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 684#64)
    (failed : (outcome original operand).result = .error .scratchExhausted)
    (reserve : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used 2 = none)
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
  have reserve' : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none := reserve
  obtain ⟨fuel, t, executed, post⟩ := arena_small_reservation_runs s base address capacity used
    hc he ha hp hbase hcapacity hused
  rcases post with failedNative | allocated
  · have frame := failedNative.2.2.frame
    have memory := failedNative.2.2.memory
    have local : MemoryFrame (localWrites original) s t := by
      intro a _
      exact congrArg (fun bytes => bytes a) memory
    have post := failure_post original t base operand owned (frame.saved_pure memory saved)
      ((frame.registers 19#5 (by decide)).trans out) (frame.code base hc)
      (frame.error.trans he) (frame.aligned ha) failedNative.2.1 failed (before.trans local)
    refine ⟨fuel + 54, ?_⟩
    rw [run_plus, executed]
    exact post
  · have impossible := allocated.1
    rw [reserve'] at impossible
    cases impossible

end SszArm.NatDivision
