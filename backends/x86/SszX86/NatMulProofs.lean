import SszX86.NatMulLargeReturn
import SszX86.NatMulTailcall
import SszX86.NatMulWordProofs

namespace SszX86.NatMul
open SszNative

/-- The complete original main image, its actual word-helper tail image, and
its actual memset callee establish the checked result and all physical frames.
Only initial ownership and linked instruction witnesses are assumptions. -/
theorem mul_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (wordCode : NatMulWord.CodeAt e (base+832))
    (memsetCode : MemsetCall.MemsetCodeAt e (base+148928))
    (s : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) :
    Eventually (step e) (Post s left right address capacity used ra) (s, base) := by
  apply eventually_trans (step e) (Prepared (bodyState s) left right base)
    (Post s left right address capacity used ra) _
    (entry_prepares e base hc s left right address capacity used ra owned)
  rintro ⟨t, pc⟩ prepared
  cases prepared with
  | zero empty frame pcEq =>
    rw [pcEq]
    exact zero_finish_cps e base hc s t left right address capacity used ra owned empty
      frame.memory frame.output (frame.stack.trans (body_stack s)) frame.simd
  | word_left leftNonzero rightOne frame pointer payload factor pcEq =>
    rw [pcEq]
    apply tailcall_cps e base hc s t left (SszNative.NatMul.lowWord right)
      frame.memory frame.output (frame.stack.trans (body_stack s)) frame.arena
      pointer payload factor frame.simd
    intro u tail
    have helperOwned := TailState.owned owned tail owned.left_at owned.left_owned
    have helperRun := NatMulWord.mul_word_correct e (base+832) wordCode u left
      (SszNative.NatMul.lowWord right) address capacity used ra helperOwned
    have same := SszNative.NatMul.run_right_one left right address.toNat capacity.toNat used.toNat
      leftNonzero rightOne
    simpa only [wordOffset] using eventually_weaken (step e)
      (NatMulWord.Post u left (SszNative.NatMul.lowWord right) address capacity used ra)
      (Post s left right address capacity used ra) (u, base+832)
      (fun _ post => TailState.post owned tail same post) helperRun
  | word_right leftOne rightNonzero rightNotOne frame pointer payload factor pcEq =>
    rw [pcEq]
    apply tailcall_cps e base hc s t right (SszNative.NatMul.lowWord left)
      frame.memory frame.output (frame.stack.trans (body_stack s)) frame.arena
      pointer payload factor frame.simd
    intro u tail
    have helperOwned := TailState.owned owned tail owned.right_at owned.right_owned
    have helperRun := NatMulWord.mul_word_correct e (base+832) wordCode u right
      (SszNative.NatMul.lowWord left) address capacity used ra helperOwned
    have same := SszNative.NatMul.run_left_one left right address.toNat capacity.toNat used.toNat
      leftOne rightNonzero rightNotOne
    simpa only [wordOffset] using eventually_weaken (step e)
      (NatMulWord.Post u right (SszNative.NatMul.lowWord left) address capacity used ra)
      (Post s left right address capacity used ra) (u, base+832)
      (fun _ post => TailState.post owned tail same post) helperRun
  | counted leftMany rightMany ready pcEq =>
    rw [pcEq]
    exact large_finish_cps e base hc memsetCode s t left right address capacity used ra owned
      leftMany rightMany ready

/-- Numerical multiplication is observed at the original result pointer after
return, together with the complete representation, allocation and ABI post. -/
theorem mul_correct_value (e : Executable) (base : Int64) (hc : CodeAt e base)
    (wordCode : NatMulWord.CodeAt e (base+832))
    (memsetCode : MemsetCall.MemsetCodeAt e (base+148928))
    (s : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) :
    Eventually (step e) (fun t => Post s left right address capacity used ra t ∧
      ∀ result, (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .ok result →
        NatArithmetic.operandAt (UintCodec.widthLoad t.1.dmem) s.regs.rdi.toNat result ∧
          result.value = left.value*right.value) (s, base) := by
  apply eventually_weaken (step e) (Post s left right address capacity used ra) _ _
    (fun _ post => ⟨post, fun result success => post.value result success⟩)
  exact mul_correct e base hc wordCode memsetCode s left right address capacity used ra owned

end SszX86.NatMul
