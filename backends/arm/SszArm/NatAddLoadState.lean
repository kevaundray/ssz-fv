import SszArm.NatAddExec
import SszArm.NatCompareMemory

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Architectural field writes commute with a byte-store without expanding any
byte of that store. This keeps lowering-block proofs independent of memory size. -/
theorem load_store_field (s : ArmState) (field : StateField) (value : state_value field)
    (bytes : Nat) (address : BitVec 64) (data : BitVec (bytes * 8)) :
    write_mem_bytes bytes address data (w field value s) =
      w field value (write_mem_bytes bytes address data s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro other
    by_cases same : other = field
    · subst other; simp only [r_of_write_mem_bytes, r_of_w_same]
    · simp only [r_of_write_mem_bytes, r_of_w_different same]
  · simp only [write_mem_bytes_program, w_program]
  · intro n pointer
    rw [read_mem_bytes_of_w]
    exact NatCompare.read_spill_w s field value n bytes pointer address data

theorem load_gpr_pc (s : ArmState) (reg : BitVec 5) (value pc : BitVec 64) :
    w (.GPR reg) value (w .PC pc s) = w .PC pc (w (.GPR reg) value s) :=
  w_of_w_commute (by intro equal; cases equal)

/-- Restoring the two temporary architectural fields leaves only the load's
actual destination changed. No enum or memory expression is unfolded here. -/
theorem load_restore_fields (s : ArmState) (tmp dst : BitVec 5) (address word : BitVec 64)
    (tmpSP : tmp ≠ 31#5) (dstSP : dst ≠ 31#5) (different : dst ≠ tmp) :
    w (.GPR 31#5) (r (.GPR 31#5) s)
      (w (.GPR tmp) (r (.GPR tmp) s)
        (w (.GPR dst) word
          (w (.GPR tmp) address (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s)))) =
      w (.GPR dst) word s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases hsp : reg = 31#5 <;> by_cases ht : reg = tmp <;>
        by_cases hd : reg = dst <;> (try subst reg) <;>
        simp_all (config := {decide := true}) [state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp only [w_program]
  · intro n pointer; simp only [read_mem_bytes_of_w]

/-- The eight architectural transforms used by each actual lowered indexed read.
This is state algebra only; binding to the fetched instructions is proved separately. -/
def indexedReadSequence (s : ArmState) (ptr index tmp dst : BitVec 5) : ArmState :=
  let s := put 31 (r (.GPR 31#5) s - 16#64) s
  let s := next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR tmp) s) s)
  let s := put tmp (r (.GPR index) s) s
  let s := put tmp (r (.GPR tmp) s <<< 3) s
  let s := put tmp (r (.GPR ptr) s + r (.GPR tmp) s) s
  let s := put dst (read_mem_bytes 8 (r (.GPR tmp) s) s) s
  let s := put tmp (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  put 31 (r (.GPR 31#5) s + 16#64) s

/-- Opaque semantics of the common save/address/load/restore lowering sequence. -/
theorem indexedReadSequence_eq (s : ArmState) (ptr index tmp dst : BitVec 5)
    (word : BitVec 64)
    (tmpSP : tmp ≠ 31#5) (dstSP : dst ≠ 31#5)
    (ptrSP : ptr ≠ 31#5) (indexSP : index ≠ 31#5)
    (ptrTmp : ptr ≠ tmp) (indexTmp : index ≠ tmp) (dstTmp : dst ≠ tmp)
    (load : read_mem_bytes 8 (r (.GPR ptr) s + (r (.GPR index) s <<< 3))
      (NatCompare.saved s tmp) = word)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s tmp) = r (.GPR tmp) s) :
    indexedReadSequence s ptr index tmp dst =
      w .PC (read_pc s + 32#64) (w (.GPR dst) word (NatCompare.saved s tmp)) := by
  have spTmp : (31#5) ≠ tmp := Ne.symm tmpSP
  have spDst : (31#5) ≠ dst := Ne.symm dstSP
  have restored := load_restore_fields (NatCompare.saved s tmp) tmp dst
    (r (.GPR ptr) s + (r (.GPR index) s <<< 3)) word tmpSP dstSP dstTmp
  simp only [NatCompare.saved, r_of_write_mem_bytes] at load restore restored ⊢
  simpa (config := {decide := true}) (disch := simp_all)
    [indexedReadSequence, put, next, load_store_field, load_gpr_pc,
      state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel,
      spTmp, spDst, load, restore] using
    congrArg (w .PC (read_pc s + 32#64)) restored

end SszArm.NatAdd
