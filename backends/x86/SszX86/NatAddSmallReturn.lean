import SszX86.NatAddBorrowReturn
import SszX86.NatAddSmallPhase

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A fitting one-word sum publishes its exact low word and restores the ABI
without reserving arena storage. The operands may have borrowed Large inputs. -/
theorem small_fit_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (ready : SumReady (pushedState s) t left right)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
    (fits : (SszNative.NatAdd.sumWide left right).toNat < 2^64) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+250) := by
  apply small_publish_cps e base hc t (ready.frame.output_mapped owned)
  have out : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by rw [ready.frame.output]; rfl
  rw [out, ready.low]
  have model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.unchanged used.toNat
        (.ok (.small ((SszNative.NatAdd.sumWide left right).setWidth 64))) := by
    rw [SszNative.NatAdd.run_one_word left right address.toNat capacity.toNat used.toNat
      leftNonzero rightNonzero small]
    simp only [NatArithmetic.fromWide, fits, ↓reduceIte]
  have zero64 : (0 : BitVec 64) = 0#64 := by decide
  simpa only [NatOperand.pointer, NatOperand.payload, zero64] using
    unchanged_memory_finish_cps e base hc s t left right address capacity used ra owned ready.frame _ model

end SszX86.NatAdd
