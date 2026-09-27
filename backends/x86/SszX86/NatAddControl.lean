import SszX86.NatAddCore

namespace SszX86.NatAdd

/-- Pure preparation cannot touch memory, stack, output/arena anchors, or SIMD.
Scratch integer registers are restored by the actual epilogue, not this frame. -/
structure ControlFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  stack : t.regs.rsp = s.regs.rsp
  output : t.regs.rdi = s.regs.rdi
  arena : t.regs.r9 = s.regs.r9
  simd : t.zmms = s.zmms

protected theorem ControlFrame.refl (s : MachineData) : ControlFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

protected theorem ControlFrame.trans {s t u : MachineData}
    (first : ControlFrame s t) (second : ControlFrame t u) : ControlFrame s u :=
  ⟨second.memory.trans first.memory, second.stack.trans first.stack,
    second.output.trans first.output, second.arena.trans first.arena,
    second.simd.trans first.simd⟩

end SszX86.NatAdd
