import SszX86.NatDivisionPrologueMemory
import SszX86.NatDivisionPrepare
import SszX86.NatDivisionWideProofs
import SszX86.NatDivisionLargeProofs

namespace SszX86.NatDivision
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete execution of the linked private Nat.div_rem_small entry through
its actual RET. Every runtime CALL composes the already-proved __udivti3 body
inside the same executable via a structural code-image witness.

The only arithmetic precondition is the production callers' divisor ≥ 2.
Original noncanonical Large representations, every checked allocation failure,
the complete written quotient buffer, normalization, borrowed input, arena
cursor, SIMD/callee-saved registers, stack and incoming return slot are retained
by the exact physical Owned/Post contract. -/
theorem divide_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + Int64.ofNat udivOffset))
    (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra) :
    Eventually (step e) (Post s operand divisor address capacity used ra)
      (s, base + Int64.ofNat entry) := by
  change Eventually (step e) (Post s operand divisor address capacity used ra) (s, base + 0)
  rw [Int64.add_zero]
  apply prologue_cps e base hc s owned.stack_mapped
  apply prepare_operand_cps e base hc (prologueState s) operand
  · exact owned.prologue_operand_registers.1
  · exact owned.prologue_operand_registers.2
  · exact owned.prologue_operand_at
  · intro count t prepared
    exact wide_phase e base hc hdiv s t operand divisor address capacity used ra owned count prepared
  · intro count flags
    exact large_phase e base hc hdiv s operand divisor address capacity used ra owned count flags

/-- The observable private ABI refines the exact shared source/resource model,
not merely an existential equal-valued quotient. -/
theorem divide_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + Int64.ofNat udivOffset))
    (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra) :
    Eventually (step e)
      (fun t => NatArithmetic.DivisionResultAt (UintCodec.widthLoad t.1.dmem) s.regs.rdi.toNat
        (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result)
      (s, base + Int64.ofNat entry) := by
  apply eventually_weaken (step e) (Post s operand divisor address capacity used ra)
  · intro t post
    exact post.observed
  · exact divide_correct e base hc hdiv s operand divisor address capacity used ra owned

end SszX86.NatDivision
