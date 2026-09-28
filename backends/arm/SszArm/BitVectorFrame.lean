import SszArm.BitVectorState
import SszArm.BitVectorExpectedExec

namespace SszArm.BitVector

open Delimited (MemoryFrame)

theorem frame_of_memory {writes : List Delimited.Span} {s t : ArmState}
    (memory : t.mem = s.mem) : MemoryFrame writes s t := by
  intro address outside
  exact congrFun memory address

theorem stack_store_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (sp : r (.GPR 31#5) c = r (.GPR 31#5) s)
    (offset bytes : Nat) (within : offset + bytes ≤ 272) (value : BitVec (bytes * 8)) :
    MemoryFrame (localWrites s) c
      (write_mem_bytes bytes (r (.GPR 31#5) c + BitVec.ofNat 64 offset) value c) := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have address : (r (.GPR 31#5) c + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 31#5) s).toNat + offset := by
    rw [sp]
    bv_omega
  have physical : (r (.GPR 31#5) c + BitVec.ofNat 64 offset).toNat + bytes ≤ 2^64 := by
    rw [address]
    omega
  have cover : Covers (localWrites s)
      [((r (.GPR 31#5) c + BitVec.ofNat 64 offset).toNat, bytes)] := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    exact ⟨((r (.GPR 31#5) s).toNat - 80, 352), by simp [localWrites],
      by rw [address]; omega, by rw [address]; omega⟩
  exact cover.frame (Delimited.store_frame c _ bytes value physical)

theorem preparation_frame (phase : Stages.CallPreparation) (c : ArmState) (base : BitVec 64)
    (writes : List Delimited.Span) : MemoryFrame writes c (phase.result c base) := by
  apply frame_of_memory
  cases phase <;> simp only [Stages.CallPreparation.result, state_simp_rules]

theorem division_status_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Working s c length) (base : BitVec 64) :
    MemoryFrame (localWrites s) c (Block.divisionStatusResult c base) := by
  have stored := stack_store_frame owned current.sp 64 16 (by decide)
    (read_mem_bytes 8 (r (.GPR 31#5) c + 152#64) c ++
      read_mem_bytes 8 (r (.GPR 31#5) c + 144#64) c)
  simpa only [MemoryFrame, Block.divisionStatusResult, state_simp_rules,
    Memory.write_mem_bytes_eq_mem_write_bytes] using stored

private theorem divided_pair_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Working s c length) (base : BitVec 64) :
    MemoryFrame (localWrites s) c (ExpectedStage.Stage.division.result c base) := by
  have stored := stack_store_frame owned current.sp 48 16 (by decide)
    (read_mem_bytes 8 (r (.GPR 31#5) c + 72#64) c ++
      read_mem_bytes 8 (r (.GPR 31#5) c + 64#64) c)
  simpa only [MemoryFrame, ExpectedStage.Stage.result, state_simp_rules] using stored

private theorem rounded_pair_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Working s c length) (base : BitVec 64) :
    MemoryFrame (localWrites s) c (ExpectedStage.Stage.rounded.result c base) := by
  have stored := stack_store_frame owned current.sp 48 16 (by decide)
    (read_mem_bytes 8 (r (.GPR 31#5) c + 152#64) c ++
      read_mem_bytes 8 (r (.GPR 31#5) c + 144#64) c)
  simpa only [MemoryFrame, ExpectedStage.Stage.result, state_simp_rules] using stored

theorem expected_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Working s c length)
    (stage : ExpectedStage.Stage) (base : BitVec 64) :
    MemoryFrame (localWrites s) c (stage.result c base) := by
  cases stage with
  | division => exact divided_pair_frame owned current base
  | rounded => exact rounded_pair_frame owned current base
  | rounding =>
    apply frame_of_memory
    simp only [ExpectedStage.Stage.result, state_simp_rules]
  | scope =>
    apply frame_of_memory
    simp only [ExpectedStage.Stage.result, state_simp_rules]

end SszArm.BitVector
