import SszArm.MeasureBitsAllocProgressive
import SszArm.MeasureBitsAllocBounded
import SszArm.MeasureBitsAllocScope

namespace SszArm.Measure.Bits.Alloc

theorem step (site : Site) (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row site op).1) :
    stepi s = effect site base op s := by
  cases site <;> cases op
  · exact progressive_loadBase_step s base code error aligned pc
  · exact progressive_loadUsed_step s base code error aligned pc
  · exact progressive_addAddress_step s base code error aligned pc
  · exact progressive_addressGuard_step s base code error aligned pc
  · exact progressive_compareAlignment_step s base code error aligned pc
  · exact progressive_alignmentGuard_step s base code error aligned pc
  · exact progressive_addPadding_step s base code error aligned pc
  · exact progressive_maskPadding_step s base code error aligned pc
  · exact progressive_subtractAddress_step s base code error aligned pc
  · exact progressive_addUsed_step s base code error aligned pc
  · exact progressive_usedGuard_step s base code error aligned pc
  · exact progressive_compareSize_step s base code error aligned pc
  · exact progressive_sizeGuard_step s base code error aligned pc
  · exact progressive_loadCapacity_step s base code error aligned pc
  · exact progressive_addSize_step s base code error aligned pc
  · exact progressive_compareCapacity_step s base code error aligned pc
  · exact progressive_capacityGuard_step s base code error aligned pc
  · exact progressive_addPointer_step s base code error aligned pc
  · exact progressive_finish0_step s base code error aligned pc
  · exact progressive_finish1_step s base code error aligned pc
  · exact progressive_finish2_step s base code error aligned pc
  · exact bounded_loadBase_step s base code error aligned pc
  · exact bounded_loadUsed_step s base code error aligned pc
  · exact bounded_addAddress_step s base code error aligned pc
  · exact bounded_addressGuard_step s base code error aligned pc
  · exact bounded_compareAlignment_step s base code error aligned pc
  · exact bounded_alignmentGuard_step s base code error aligned pc
  · exact bounded_addPadding_step s base code error aligned pc
  · exact bounded_maskPadding_step s base code error aligned pc
  · exact bounded_subtractAddress_step s base code error aligned pc
  · exact bounded_addUsed_step s base code error aligned pc
  · exact bounded_usedGuard_step s base code error aligned pc
  · exact bounded_compareSize_step s base code error aligned pc
  · exact bounded_sizeGuard_step s base code error aligned pc
  · exact bounded_loadCapacity_step s base code error aligned pc
  · exact bounded_addSize_step s base code error aligned pc
  · exact bounded_compareCapacity_step s base code error aligned pc
  · exact bounded_capacityGuard_step s base code error aligned pc
  · exact bounded_addPointer_step s base code error aligned pc
  · exact bounded_finish0_step s base code error aligned pc
  · exact bounded_finish1_step s base code error aligned pc
  · exact bounded_finish2_step s base code error aligned pc
  · exact scope_loadBase_step s base code error aligned pc
  · exact scope_loadUsed_step s base code error aligned pc
  · exact scope_addAddress_step s base code error aligned pc
  · exact scope_addressGuard_step s base code error aligned pc
  · exact scope_compareAlignment_step s base code error aligned pc
  · exact scope_alignmentGuard_step s base code error aligned pc
  · exact scope_addPadding_step s base code error aligned pc
  · exact scope_maskPadding_step s base code error aligned pc
  · exact scope_subtractAddress_step s base code error aligned pc
  · exact scope_addUsed_step s base code error aligned pc
  · exact scope_usedGuard_step s base code error aligned pc
  · exact scope_compareSize_step s base code error aligned pc
  · exact scope_sizeGuard_step s base code error aligned pc
  · exact scope_loadCapacity_step s base code error aligned pc
  · exact scope_addSize_step s base code error aligned pc
  · exact scope_compareCapacity_step s base code error aligned pc
  · exact scope_capacityGuard_step s base code error aligned pc
  · exact scope_addPointer_step s base code error aligned pc
  · exact scope_finish0_step s base code error aligned pc
  · exact scope_finish1_step s base code error aligned pc
  · exact scope_finish2_step s base code error aligned pc

@[simp] theorem effect_program (site : Site) (op : Op) (s : ArmState) (base : BitVec 64) :
    (effect site base op s).program = s.program := by
  cases site <;> cases op <;>
    simp [effect, put, next, commit, storeWords, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem effect_error (site : Site) (op : Op) (s : ArmState) (base : BitVec 64) :
    read_err (effect site base op s) = read_err s := by
  cases site <;> cases op <;>
    simp [effect, put, next, commit, storeWords, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem effect_sp (site : Site) (op : Op) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (effect site base op s) = r (.GPR 31#5) s := by
  cases site <;> cases op <;>
    simp [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
      Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem effect_aligned (site : Site) (op : Op) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (effect site base op s) := by
  simpa only [CheckSPAlignment, state_simp_rules, effect_sp] using aligned

def block (site : Site) (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun state op => effect site base op state) s

def Follows (site : Site) (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 (row site op).1 ∧
      Follows site base ops (effect site base op s)

theorem block_run (site : Site) (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows site base ops s) :
    run ops.length s = block site base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block site base ops (effect site base op s)
    rw [run, step site op s base code error aligned follows.1]
    exact induction _ (code.congr (effect_program site op s base))
      ((effect_error site op s base).trans error)
      (effect_aligned site op s base aligned) follows.2

end SszArm.Measure.Bits.Alloc
