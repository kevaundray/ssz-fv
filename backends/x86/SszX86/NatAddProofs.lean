import SszX86.NatAddPrepare
import SszX86.NatAddSmallComplete
import SszX86.NatAddLargeReturn

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem prepared_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (t : MachineState) (prepared : Prepared (pushedState s) left right base t) :
    Eventually (step e) (Post s left right address capacity used ra) t := by
  rcases t with ⟨t, pc⟩
  cases prepared with
  | zero_left zero frame pointer payload pcEq =>
    rw [pcEq]
    exact zero_left_finish_cps e base hc s t left right address capacity used ra owned frame zero pointer payload
  | zero_right leftNonzero zero frame pointer payload pcEq =>
    rw [pcEq]
    exact zero_right_finish_cps e base hc s t left right address capacity used ra owned frame
      leftNonzero zero pointer payload
  | counted leftNonzero rightNonzero ready pcEq =>
    rw [pcEq]
    have originals := pushed_operands s left right address capacity used ra owned
    apply selection_cps e base hc (pushedState s) t left right originals.1 originals.2
      leftNonzero rightNonzero ready
    · intro small u summed
      exact sum_finish_cps e base hc s u left right address capacity used ra owned summed
        leftNonzero rightNonzero small
    · intro large u counted
      exact large_finish_cps e base hc s u left right address capacity used ra owned counted
        leftNonzero rightNonzero large
  | summed leftNonzero rightNonzero small ready pcEq =>
    rw [pcEq]
    exact sum_finish_cps e base hc s t left right address capacity used ra owned ready
      leftNonzero rightNonzero small

/-- Complete actual entry0-through-RET refinement. The only premises are the
linked instruction image and physical ownership, with arbitrary Small/Large
representations, redundant high zeros, read-only aliases and unsigned capacity. -/
theorem add_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) :
    Eventually (step e) (Post s left right address capacity used ra) (s,base) := by
  apply pushes_cps e base hc s owned.stack_mapped
  have originals := pushed_operands s left right address capacity used ra owned
  exact eventually_trans (step e) (Prepared (pushedState s) left right base)
    (Post s left right address capacity used ra) (pushedState s,base+10)
    (prepare_runs e base hc (pushedState s) left right owned.left_pointer owned.left_payload
      owned.right_pointer owned.right_payload originals.1 originals.2)
    (fun t prepared => prepared_finish_cps e base hc s left right address capacity used ra owned t prepared)

/-- The value equation concerns the exact representation observed in the actual
output, while retaining the complete allocator, frame and ABI postcondition. -/
theorem add_correct_value (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) :
    Eventually (step e)
      (fun t => Post s left right address capacity used ra t ∧
        ∀ result, (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .ok result →
          NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rdi.toNat result ∧
          result.value = left.value + right.value) (s,base) := by
  apply eventually_weaken (step e) (Post s left right address capacity used ra) _ (s,base)
    (fun _ post => ⟨post, fun result success => post.value result success⟩)
  exact add_correct e base hc s left right address capacity used ra owned

end SszX86.NatAdd
