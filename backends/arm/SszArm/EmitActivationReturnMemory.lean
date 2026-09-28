import SszArm.EmitActivationReturnStatus

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)
open Delimited (Span Protected MemoryFrame)

theorem saved_protected_body {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) :
    Protected (bodyWrites args size) (args.stack.toNat - 80) 80 := by
  have low := owned.stackLow
  have resultApart : args.result.toNat + 68 ≤ args.stack.toNat - 80 ∨
      args.stack.toNat ≤ args.result.toNat := by
    rcases owned.resultStack with empty | separate
    · omega
    · have apart := separate (args.stack.toNat - 80, 80) (by simp [stackWrites])
      simp only [Prod.fst, Prod.snd] at apart
      omega
  right
  intro span member
  simp only [bodyWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | output
  · simp only [Prod.fst, Prod.snd]
    right
    omega
  · simp only [Prod.fst, Prod.snd]
    omega
  · by_cases zero : size = 0
    · simp [zero] at output
    · simp only [zero, ↓reduceIte, List.mem_singleton] at output
      subst span
      have fitting := owned.fitting
      rcases owned.outputStack with empty | separate
      · omega
      · have apart := separate (args.stack.toNat - 80, 80) (by simp [stackWrites])
        simp only [Prod.fst, Prod.snd] at apart ⊢
        omega

theorem saved_protected_status {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) :
    Protected (statusWrites args) (args.stack.toNat - 80) 80 := by
  have low := owned.stackLow
  have resultApart : args.result.toNat + 68 ≤ args.stack.toNat - 80 ∨
      args.stack.toNat ≤ args.result.toNat := by
    rcases owned.resultStack with empty | separate
    · omega
    · have apart := separate (args.stack.toNat - 80, 80) (by simp [stackWrites])
      simp only [Prod.fst, Prod.snd] at apart
      omega
  right
  intro span member
  simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem saved_word_preserved {s t : ArmState} {args : Args} {writes : List Span}
    (frame : MemoryFrame writes s t) (low : 176 ≤ args.stack.toNat)
    (ownership : Protected writes (args.stack.toNat - 80) 80)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (args.bodySP + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (args.bodySP + BitVec.ofNat 64 offset) s := by
  have offsets : 80 ≤ offset ∧ offset + 8 ≤ 160 := by
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with h | h | h | h | h | h | h | h | h | h <;> omega
  have position : (args.bodySP + BitVec.ofNat 64 offset).toNat = args.stack.toNat - 80 + (offset - 80) := by
    simp only [Args.bodySP]
    bv_omega
  apply frame.read
  · rw [position]
    have bound := args.stack.isLt
    omega
  · rw [position]
    exact ownership.subspan (offset - 80) 8 (by omega)

theorem length_protected_status {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) : Protected (statusWrites args) args.result.toNat 8 := by
  right
  intro span member
  simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rcases owned.resultStack with empty | separate
    · omega
    · have apart := separate (args.stack.toNat - 176, 16) (by simp [stackWrites])
      simp only [Prod.fst, Prod.snd] at apart ⊢
      omega
  · simp only [Prod.fst, Prod.snd]
    omega

theorem output_protected_status {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) : Protected (statusWrites args) args.output.toNat size := by
  by_cases zero : size = 0
  · exact Or.inl zero
  · right
    intro span member
    simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    have fitting := owned.fitting
    rcases member with rfl | rfl
    · rcases owned.outputStack with empty | separate
      · omega
      · have apart := separate (args.stack.toNat - 176, 16) (by simp [stackWrites])
        simp only [Prod.fst, Prod.snd] at apart ⊢
        omega
    · rcases owned.outputResult with empty | separate
      · omega
      · have apart := separate (args.result.toNat + 64, 4) (by simp)
        simp only [Prod.fst, Prod.snd] at apart ⊢
        omega

end SszArm.Emit
