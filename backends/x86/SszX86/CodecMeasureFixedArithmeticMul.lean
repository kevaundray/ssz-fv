import SszX86.CodecMeasureFixedArithmeticCall
import SszX86.NatMulProofs

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Vector width multiplication executes the original helper, its word tail image,
and the actual memset lowering; the full provider Post retains allocation effects. -/
theorem mul581_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (mulCode : NatMul.CodeAt e (base + Int64.ofInt (-61792)))
    (wordCode : NatMulWord.CodeAt e ((base + Int64.ofInt (-61792)) + 832))
    (memsetCode : MemsetCall.MemsetCodeAt e ((base + Int64.ofInt (-61792)) + 148928))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatMul.Owned (arithmeticCallState s (base + 586).toBitVec)
      left right address capacity used (base + 586).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatMul.Post (arithmeticCallState s (base + 586).toBitVec)
      left right address capacity used (base + 586).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 581) := by
  apply call581 e base hc s P hmap
  exact eventually_trans (step e)
    (NatMul.Post (arithmeticCallState s (base + 586).toBitVec)
      left right address capacity used (base + 586).toBitVec) P _
    (NatMul.mul_correct e (base + Int64.ofInt (-61792)) mulCode wordCode memsetCode
      (arithmeticCallState s (base + 586).toBitVec) left right address capacity used
      (base + 586).toBitVec owned) next

end SszX86.CodecMeasureFixed
