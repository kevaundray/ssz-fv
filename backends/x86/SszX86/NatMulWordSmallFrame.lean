import SszX86.NatMulWordSmallState

namespace SszX86.NatMulWord

theorem PureFrame.after_reserve {s t u : MachineData} (first : PureFrame s t)
    (second : SmallReservation.Frame t u) : PureFrame s u := by
  have rsp := second.registers .rsp (by decide) (by decide) (by decide) (by decide)
  have rdi := second.registers .rdi (by decide) (by decide) (by decide) (by decide)
  have r8 := second.registers .r8 (by decide) (by decide) (by decide) (by decide)
  refine ⟨second.memory.trans first.memory, ?_, ?_, ?_, second.vectors.trans first.simd⟩
  · exact rsp.trans first.sp
  · exact (UInt64.toBitVec_inj.mp rdi).trans first.output
  · exact (UInt64.toBitVec_inj.mp r8).trans first.arena

theorem WideReady.after_reserve {s t u : MachineData} {wide : BitVec 128}
    (first : WideReady s t wide) (second : SmallReservation.Frame t u) : WideReady s u wide := by
  have low := second.registers .rax (by decide) (by decide) (by decide) (by decide)
  have high := second.registers .rdx (by decide) (by decide) (by decide) (by decide)
  exact ⟨first.toPureFrame.after_reserve second, low.trans first.low, high.trans first.high⟩

end SszX86.NatMulWord
