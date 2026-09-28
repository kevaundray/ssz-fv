import SszX86.NatMulReserveOwnership
import SszX86.NatMulReserveGeometry
import SszX86.NatMulReserveCursor

namespace SszX86.NatMul.Reservation
open SszNative

/-- Complete main-allocation CPS boundary from the actual active scan state.
Both continuation alternatives are proved from original physical ownership;
there is no successful reserve, initialized buffer, or helper-exit premise. -/
theorem complete_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemsetCall.MemsetCodeAt e (base + 148928))
    (original current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64)
    (owned : Owned original left right address capacity used ra)
    (memory : current.dmem = pushedMem original)
    (stack : current.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 88#64)
    (arena : current.regs.r9 = original.regs.r9)
    (lc : current.regs.r12.toNat = left.wordCount)
    (rc : current.regs.r13.toNat = right.wordCount)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (P : MachineState → Prop)
    (failure : ∀ t, Failed current base address capacity used t →
      SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
        NatArithmetic.unchanged used.toNat (.error .scratchExhausted) →
      Eventually (step e) P t)
    (success : ∀ r guardFlags fillFlags t,
      SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
        NatArithmetic.committed r (SszNative.NatMul.writtenWords left right) →
      MemsetCall.Post (initializedState current address used guardFlags fillFlags)
        (base + 493).toBitVec (8 * (left.wordCount + right.wordCount)) t →
      Eventually (step e) P t) :
    Eventually (step e) P (current, base + 275) := by
  have header := header_of_active original current left right address capacity used ra owned memory arena
  have storage := storage_of_active original current left right address capacity used ra owned memory stack
  have run := large_runs e base hc helper current address capacity used left right lc rc hl hr header storage
  apply eventually_trans _ _ _ _ run
  intro t post
  rcases post with ⟨failed, outcome⟩ | ⟨r, guardFlags, fillFlags, outcome, initialized⟩
  · exact failure t failed outcome
  · exact success r guardFlags fillFlags t outcome initialized

end SszX86.NatMul.Reservation
