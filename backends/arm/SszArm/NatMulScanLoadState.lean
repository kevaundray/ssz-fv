import SszArm.NatMulScanFrame

namespace SszArm.NatMul

/-- State-independent seven-transform lowering used by the right scan. -/
def offsetReadSequence (s : ArmState) (ptr tmp dst : BitVec 5) (offset : BitVec 64) : ArmState :=
  let s := put 31 (r (.GPR 31#5) s - 16#64) s
  let s := next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR tmp) s) s)
  let s := put tmp (r (.GPR ptr) s + 0#64) s
  let s := put tmp (r (.GPR tmp) s - offset) s
  let s := put dst (read_mem_bytes 8 (r (.GPR tmp) s) s) s
  let s := put tmp (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  put 31 (r (.GPR 31#5) s + 16#64) s

theorem offsetReadSequence_eq (s : ArmState) (ptr tmp dst : BitVec 5)
    (offset word : BitVec 64)
    (tmpSP : tmp ≠ 31#5) (dstSP : dst ≠ 31#5)
    (ptrSP : ptr ≠ 31#5) (ptrTmp : ptr ≠ tmp) (dstTmp : dst ≠ tmp)
    (load : read_mem_bytes 8 (r (.GPR ptr) s - offset) (NatCompare.saved s tmp) = word)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s tmp) = r (.GPR tmp) s) :
    offsetReadSequence s ptr tmp dst offset =
      w .PC (read_pc s + 28#64) (w (.GPR dst) word (NatCompare.saved s tmp)) := by
  have spTmp : (31#5) ≠ tmp := Ne.symm tmpSP
  have spDst : (31#5) ≠ dst := Ne.symm dstSP
  have restored := NatAdd.load_restore_fields (NatCompare.saved s tmp) tmp dst
    (r (.GPR ptr) s - offset) word tmpSP dstSP dstTmp
  simp only [NatCompare.saved, r_of_write_mem_bytes] at load restore restored ⊢
  simpa (config := {decide := true}) (disch := simp_all)
    [offsetReadSequence, put, next, NatAdd.load_store_field, NatAdd.load_gpr_pc,
      state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel,
      spTmp, spDst, load, restore] using
    congrArg (w .PC (read_pc s + 28#64)) restored

end SszArm.NatMul
