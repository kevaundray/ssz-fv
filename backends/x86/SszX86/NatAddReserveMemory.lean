import SszX86.NatAddReserve
import SszX86.NatAddInitialMemory
import SszX86.NatAddCommitMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem ControlFrame.arena_mapped {s t : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) : Large.Mapped t.dmem address capacity.toNat := by
  rw [frame.memory]
  change Large.Mapped (pushedMem s) address capacity.toNat
  unfold pushedMem Delimited.pushedMem
  repeat' first | exact owned.arena_mapped | apply Large.mapped_store

theorem ControlFrame.small_header {s t : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) : Reservation.Small.Header t address capacity used := by
  have arena : t.regs.r9 = s.regs.r9 := frame.arena
  have header := pushed_header s left right address capacity used ra owned
  have eight : (8 : BitVec 64) = 8#64 := by decide
  have sixteen : (16 : BitVec 64) = 16#64 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.memory, arena]
    exact header.1
  · rw [frame.memory, arena]
    change Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec+8#64) 8 = some (capacity.toNat : Int)
    simpa only [eight] using header.2.1
  · rw [frame.memory, arena]
    change Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec+16#64) 8 = some (used.toNat : Int)
    simpa only [sixteen] using header.2.2

theorem ControlFrame.large_header {s t : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) : Reservation.Large.Header t address capacity used := by
  have header := frame.small_header owned
  exact ⟨header.address_load, header.capacity_load, header.used_load⟩

theorem Reservation.Small.Frame.control {s t : MachineData} (frame : Reservation.Small.Frame s t)
    (memory : t.dmem = s.dmem) : ControlFrame s t := by
  refine ⟨memory, ?_, ?_, ?_, frame.1⟩
  · apply UInt64.toBitVec_inj.mp
    exact frame.2 .rsp (by decide) (by decide) (by decide) (by decide)
  · apply UInt64.toBitVec_inj.mp
    exact frame.2 .rdi (by decide) (by decide) (by decide) (by decide)
  · apply UInt64.toBitVec_inj.mp
    exact frame.2 .r9 (by decide) (by decide) (by decide) (by decide)

theorem Reservation.Large.Frame.control {s t : MachineData} (frame : Reservation.Large.Frame s t)
    (memory : t.dmem = s.dmem) : ControlFrame s t := by
  refine ⟨memory, ?_, ?_, ?_, frame.1⟩
  · apply UInt64.toBitVec_inj.mp
    exact frame.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · apply UInt64.toBitVec_inj.mp
    exact frame.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · apply UInt64.toBitVec_inj.mp
    exact frame.2 .r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SszX86.NatAdd
