import SszArm.MeasureBitsWidthOps
import SszArm.MeasureBitVectorCompareInstructions

namespace SszArm.Measure.Bits.Width

open Result

theorem low1852_effect (s : ArmState) :
    p1852.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s) :=
  BitVector.compare3272_effect s

theorem low1856_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1856.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s) :=
  BitVector.compare3276_effect s aligned

theorem low1860_effect (s : ArmState) :
    p1860.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (r (.GPR 26#5) s >>> (3 : Nat)) s) := by
  change exec_inst (.DPI (.Bitfield
    { sf := 1, opc := 2, N := 1, immr := 3, imms := 63, Rn := 26, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      UintCodec.uint_and_ones, UintCodec.uint_lsr3_mask, NatExact.gpr_w_pc]

theorem low1864_effect (s : ArmState) :
    p1864.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 8#5) (r (.GPR 9#5) s ||| (r (.GPR 25#5) s <<< (61 : Nat))) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 25, imm6 := 61, Rn := 9, Rd := 8 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem low1868_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1868.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) :=
  BitVector.compare3300_effect s aligned

theorem low1872_effect (s : ArmState) :
    p1872.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) :=
  BitVector.compare3304_effect s

end SszArm.Measure.Bits.Width
