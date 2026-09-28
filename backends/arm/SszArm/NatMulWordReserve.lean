import SszArm.NatMulWordReserveModel
import SszArm.NatMulWordReserveFirst

namespace SszArm.NatMulWord.Reserve

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Resource ownership is stated over the original free suffix, not a future
reservation. Guards derive the smaller actual payload write interval. -/
def currentWrites (s : ArmState) (address capacity used : BitVec 64) : List Delimited.Span :=
  [((r (.GPR 4#5) s + 16#64).toNat, 8),
    (address.toNat + used.toNat, capacity.toNat - used.toNat)]

theorem wide_input_owned {s t : ArmState} {address capacity used : BitVec 64}
    (reached : Checkpoint s t)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2)
    (pointer : (widePointer t).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat)
    (operand : SszNative.NatOperand)
    (owned : NatAdd.OperandOwned (currentWrites s address capacity used) operand) :
    NatAdd.OperandOwned (wideCommitWrites t) operand := by
  cases operand with
  | small value => trivial
  | large p words =>
    change Delimited.Protected _ _ _ at owned ⊢
    rcases owned with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      have hdr := reached.frame.registers 4#5 (by decide)
      simp only [wideCommitWrites, List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl
      · rw [hdr]
        exact separate ((r (.GPR 4#5) s + 16#64).toNat, 8) (by simp [currentWrites])
      · have apart := separate (address.toNat + used.toNat, capacity.toNat - used.toNat)
          (by simp [currentWrites])
        have start := SszNative.Arena.used_le_start address.toNat used.toNat
        have finish := checks.2.2.2.2.2
        change SszNative.Arena.start address.toNat used.toNat + 16 ≤ capacity.toNat at finish
        rw [pointer]
        omega

/-- Complete width-two prefix, from the original guard PC through the actual
cursor and paired limb stores. Failure has no memory writes at all. -/
theorem wide_reserve_commit_runs (s : ArmState) (base address capacity used : BitVec 64)
    (operand : SszNative.NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 1132#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 4#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s = used)
    (owned : ArenaOwned s address capacity used)
    (input : operand.At (widthLoad s))
    (inputOwned : NatAdd.OperandOwned (currentWrites s address capacity used) operand) :
    ∃ fuel t, run fuel s = t ∧
      ((Checkpoint s t ∧ SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none ∧
          read_pc t = base + 1264#64) ∨
        (∃ u, Checkpoint s u ∧ WideSpace u ∧
          SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2 ∧
          read_pc u = base + 1200#64 ∧ t = block base wideCommitOps u ∧
          (widePointer u).toNat = address.toNat + SszNative.Arena.start address.toNat used.toNat ∧
          read_pc t = base + 1216#64 ∧ r (.GPR 10#5) t = widePointer u ∧ r (.GPR 8#5) t = 2#64 ∧
          (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = SszNative.Arena.finish address.toNat used.toNat 2 ∧
          read_mem_bytes 8 (r (.GPR 4#5) s) t = address ∧
          read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t = capacity ∧
          MemoryFrame (wideCommitWrites u) s t ∧ NatAdd.OperandPreserved s t operand ∧
          (SszNative.NatOperand.large (widePointer u) [r (.GPR 8#5) s, r (.GPR 9#5) s]).At (widthLoad t))) := by
  obtain ⟨fuel, u, hrun, reached, selected⟩ := wide_checks_runs s base address capacity used
    hc he ha hp headerBase headerCapacity headerUsed
  rcases selected with ⟨failed, exit⟩ | ⟨checks, exit, baseReg, startReg, finishReg, _, _⟩
  · exact ⟨fuel, u, hrun, Or.inl ⟨reached, failed, exit⟩⟩
  · obtain ⟨space, pointer⟩ := owned.wideSpace reached checks baseReg startReg
    let t := block base wideCommitOps u
    have committed := wide_commit_run u base (reached.frame.code base hc)
      (reached.frame.error.trans he) (reached.frame.aligned ha) exit
    have effect := wide_commit_effect u base exit
    have memory := wide_commit_memory u base space exit
    have before : MemoryFrame (wideCommitWrites u) s u := by
      intro a _
      exact congrFun reached.memory a
    have frame : MemoryFrame (wideCommitWrites u) s t := before.trans memory.1
    have inputSpace := wide_input_owned reached checks pointer operand inputOwned
    have preserved := NatAdd.operand_preserved frame operand input inputSpace
    have hdr := reached.frame.registers 4#5 (by decide)
    have low := reached.frame.registers 8#5 (by decide)
    have high := reached.frame.registers 9#5 (by decide)
    refine ⟨fuel + 4, t, by rw [run_plus, hrun, committed], Or.inr
      ⟨u, reached, space, checks, exit, rfl, pointer, effect.1, effect.2.1, effect.2.2.1,
        ?_, ?_, ?_, frame, preserved, ?_⟩⟩
    · rw [← hdr, memory.2.1]
      exact finishReg
    · rw [← hdr, memory.2.2.1]
      simpa using (reached.header 0#64).trans (by simpa using headerBase)
    · rw [← hdr, memory.2.2.2.1]
      exact (reached.header 8#64).trans headerCapacity
    · simpa only [low, high] using memory.2.2.2.2

/-- Input preservation on every large guard exit, including the signed-size
spill, follows from ownership of the current stack slot alone. -/
theorem large_prefix_input {s t : ArmState} (reached : Prefix s t)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) (operand : SszNative.NatOperand)
    (input : operand.At (widthLoad s))
    (owned : NatAdd.OperandOwned [((r (.GPR 31#5) s).toNat - 16, 8)] operand) :
    NatAdd.OperandPreserved s t operand :=
  NatAdd.operand_preserved (reached.memoryFrame stack) operand input owned

end SszArm.NatMulWord.Reserve
