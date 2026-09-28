import SszArm.MeasureActivationPrologue
import SszArm.EmitMemory

namespace SszArm.Measure

open Delimited (Span Protected MemoryFrame)

theorem saved_word_preserved {s t : ArmState} {args : Args} {writes : List Span}
    (frame : MemoryFrame writes s t) (low : 288 ≤ args.stack.toNat)
    (ownership : Protected writes (args.stack.toNat - 80) 80)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (args.bodySP + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (args.bodySP + BitVec.ofNat 64 offset) s := by
  have offsets : 192 ≤ offset ∧ offset + 8 ≤ 272 := by
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with h | h | h | h | h | h | h | h | h | h <;> omega
  have position : (args.bodySP + BitVec.ofNat 64 offset).toNat = args.stack.toNat - 80 + (offset - 192) := by
    simp only [Args.bodySP]
    bv_omega
  apply frame.read
  · rw [position]
    have bound := args.stack.isLt
    omega
  · rw [position]
    exact ownership.subspan (offset - 192) 8 (by omega)

end SszArm.Measure
