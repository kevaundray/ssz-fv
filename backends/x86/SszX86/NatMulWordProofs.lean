import SszX86.NatMulWordDispatch
import SszX86.NatMulWordLargeComplete

namespace SszX86.NatMulWord
open SszNative

/-- Complete original mul_word entry-to-RET refinement for every physically
owned raw representation and scalar. All loop and allocation facts are derived
from the initial ownership and checked model, never assumed at a future cut. -/
theorem mul_word_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra) :
    Eventually (step e) (Post s operand factor address capacity used ra) (s, base) := by
  apply mul_word_dispatch e base hc s operand factor address capacity used ra owned
  intro nonzero notone t large ready
  exact large_multiply_cps e base hc s t operand factor address capacity used ra owned nonzero notone large ready

theorem mul_word_correct_value (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra) :
    Eventually (step e) (fun t => Post s operand factor address capacity used ra t ∧
      ∀ result, (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result = .ok result →
        NatArithmetic.operandAt (UintCodec.widthLoad t.1.dmem) s.regs.rdi.toNat result ∧
          result.value = operand.value*factor.toNat) (s, base) := by
  apply eventually_weaken (step e) (Post s operand factor address capacity used ra) _ _
    (fun _ post => ⟨post, fun result success => post.value result success⟩)
  exact mul_word_correct e base hc s operand factor address capacity used ra owned

end SszX86.NatMulWord
