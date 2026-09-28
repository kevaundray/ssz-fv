import SszX86.EmitEntryState

namespace SszX86.Emit

theorem select_bool (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (tag : s.regs.rax.toBitVec = 0#64)
    (next : ∀ af, Eventually (step e) P (descriptorTested s af, base + 190)) :
    Eventually (step e) P (s, base + 32) := by
  apply descriptor_zero_branch e base hc s P
  intro af
  simpa [tag] using next af

theorem select_uint (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (tag : s.regs.rax.toBitVec = 1#64)
    (next : Eventually (step e) P (descriptorCompared s, base + 50)) :
    Eventually (step e) P (s, base + 32) := by
  apply descriptor_zero_branch e base hc s P
  intro af
  simp only [tag, show ((1#64 : BitVec 64) == 0#64) = false by decide]
  apply descriptor_one_branch e base hc
  simpa [descriptorTested, descriptorCompared, tag,
    show (1#64).take 32 = 1#32 by decide] using next

theorem select_other (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (nonzero : s.regs.rax.toBitVec ≠ 0#64)
    (notOne : s.regs.rax.toBitVec.take 32 ≠ 1#32)
    (next : Eventually (step e) P (descriptorCompared s, base + 228)) :
    Eventually (step e) P (s, base + 32) := by
  apply descriptor_zero_branch e base hc s P
  intro af
  simp only [beq_eq_false_iff_ne.mpr nonzero]
  apply descriptor_one_branch e base hc
  simpa [descriptorTested, descriptorCompared, notOne] using next

end SszX86.Emit
