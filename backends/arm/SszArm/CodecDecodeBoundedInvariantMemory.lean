import SszArm.CodecDecodeBoundedInvariant
import SszArm.CodecDecodeBoundedErrorMemory

namespace SszArm.Codec.Decode.Bounded

open Delimited (Protected MemoryFrame)
open SszNative

/-- Actual saved slots sit above lowering scratch and are separated only from
the meaningful result record. No ownership is imposed on the stack gap. -/
theorem saved_protected {s t : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (active : Activation s t)
    (output : r (.GPR 19#5) t = r (.GPR 0#5) s)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    Protected (errorWrites t) (bodySP s + BitVec.ofNat 64 offset).toNat 8 := by
  have low := owned.stackBound
  have high := owned.resultBound
  rcases owned.outputStack with empty | separate
  · omega
  have link := separate ((r (.GPR 31#5) s).toNat - 48, 8) (by simp [stackWrites])
  have saved := separate ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [stackWrites])
  simp only [Prod.fst, Prod.snd] at link saved
  right
  intro span writes
  simp only [errorWrites, List.mem_cons, List.not_mem_nil, or_false] at writes
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases writes with rfl | rfl
  all_goals
    simp only [Prod.fst, Prod.snd, active.stack, output]
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp only [bodySP]; bv_omega

theorem saved_physical (s : ArmState) (low : 64 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    (bodySP s + BitVec.ofNat 64 offset).toNat + 8 ≤ 2 ^ 64 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [bodySP]; bv_omega

/-- A proved local byte frame transports the saved image. In particular this
covers the comparison spill and both result-store paths without assuming a
future restore or weakening the architectural calling convention. -/
theorem Activation.written {s t u : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (active : Activation s t)
    (output : r (.GPR 19#5) t = r (.GPR 0#5) s)
    (memory : MemoryFrame (errorWrites t) t u)
    (stack : r (.GPR 31#5) u = r (.GPR 31#5) t)
    (registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
      reg ∉ [19#5, 20#5, 21#5, 22#5, 30#5] → r (.GPR reg) u = r (.GPR reg) t)
    (vectors : ∀ reg : BitVec 5, r (.SFP reg) u = r (.SFP reg) t)
    (program : u.program = t.program) (error : read_err u = read_err t) : Activation s u := by
  refine ⟨stack.trans active.stack, ?_, ?_, ?_, program.trans active.program,
    error.trans active.error⟩
  · intro reg offset member
    rw [memory.read _ 8 (saved_physical s owned.stackBound reg offset member)
      (saved_protected owned active output reg offset member)]
    exact active.saved reg offset member
  · intro reg low high outside
    exact (registers reg low high outside).trans (active.registers reg low high outside)
  · intro reg
    exact (vectors reg).trans (active.vectors reg)

end SszArm.Codec.Decode.Bounded
