import SszArm.EmitBitsPayload
import SszArm.EmitBitsStoredSuffix

namespace SszArm.Emit.Bits

open SszNative.Serialize (Packed)
open SszNative (NatOperand)
open UintCodec (widthLoad)

theorem vector_tail_suffix (s : ArmState) (base : BitVec 64) (args : Args)
    (length : NatOperand) (bits : Packed) (size : Nat)
    (owned : Owned s args (.bitVector length) (.bits bits) size)
    (work : WorkRegisters s args .vector bits) (hasTail : bits.count.toNat % 8 ≠ 0)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad s (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1256#64) :
    ∃ t, run 28 s = t ∧ Produced s t args (.bitVector length) (.bits bits) size base := by
  let a := tailGuarded .vectorBacking s
  let b := tailGuarded .vectorCapacity a
  have sizeEq := vector_size owned.expected
  have backing := (backing_guards bits).2.2 hasTail
  have live : bits.count.toNat / 8 < size := by omega
  have backingGood : TailGuard.good .vectorBacking s := by
    change (r (.GPR 23#5) s).toNat < (r (.GPR 24#5) s).toNat
    rw [work.full, work.backing, backing]
    omega
  have aRun := tail_guard_run .vectorBacking s base code error aligned pc
  have aPC : read_pc a = base + 1264#64 := by
    rw [tailGuarded_pc .vectorBacking s backingGood, pc]
    simp [BitVec.add_assoc]
  have aWork := work.of_memory owned (tailGuarded_memory .vectorBacking s)
    (fun reg _ => tailGuarded_register .vectorBacking s reg)
  have aInput : Owned a args (.bitVector length) (.bits bits) size := owned.of_mem_eq (tailGuarded_memory _ _)
  have aCode : CodeAt a base := by simpa only [a, CodeAt, tailGuarded_program] using code
  have aError : read_err a = .None := (tailGuarded_error .vectorBacking s).trans error
  have aAligned := aligned_of_stack aligned (tailGuarded_register .vectorBacking s 31#5)
  have capacityGood : TailGuard.good .vectorCapacity a := by
    change (r (.GPR 23#5) a).toNat < (r (.GPR 21#5) a).toNat
    rw [aWork.full, aWork.capacity]
    exact vector_tail_guard aInput hasTail
  have bRun := tail_guard_run .vectorCapacity a base aCode aError aAligned aPC
  have bPC : read_pc b = base + 1272#64 := by
    rw [tailGuarded_pc .vectorCapacity a capacityGood, aPC]
    simp [BitVec.add_assoc]
  have bMemory : b.mem = s.mem := by simp [b, a]
  have bInput : Owned b args (.bitVector length) (.bits bits) size := owned.of_mem_eq bMemory
  have bRegisters (reg : BitVec 5) : r (.GPR reg) b = r (.GPR reg) s := by simp [b, a]
  have bWork := work.of_memory owned bMemory (fun reg _ => bRegisters reg)
  have bCode : CodeAt b base := by simpa only [b, CodeAt, tailGuarded_program] using aCode
  have bError : read_err b = .None := (tailGuarded_error .vectorCapacity a).trans aError
  have bAligned := aligned_of_stack aligned (bRegisters 31#5)
  obtain ⟨u, payloadRun, payload⟩ := payload_run .vector b base args (.bitVector length) bits size
    trivial bInput bWork hasTail bCode bError bAligned bPC
  have uCode : CodeAt u base := by simpa only [CodeAt, payload.program] using bCode
  have uAligned := aligned_of_stack aligned (payload.work.stack.trans work.stack.symm)
  have uPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad u (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat := by
    intro index before
    rw [payload.output index before, load_eq_of_mem_eq bMemory]
    exact copiedPrefix index before
  obtain ⟨t, storedRun, post⟩ := stored_suffix u base args (.bitVector length) bits size trivial
    payload.owned payload.work live payload.byte uPrefix uCode payload.error uAligned payload.pc
  refine ⟨t, ?_, ?_⟩
  · change run (2 + (2 + (15 + 9))) s = _
    rw [run_plus, aRun, run_plus, bRun, run_plus, payloadRun]
    exact storedRun
  · apply produced_prepend post
    · exact payload.program.trans (by simp [b, a])
    · intro address outside
      exact (payload.frame address outside).trans (congrFun bMemory address)
    · intro reg member
      have untouched : reg ∉ [8#5, 9#5, 10#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      exact (payload.registers reg untouched).trans (bRegisters reg)
    · intro reg low high
      rw [payload.vectors]
      simp [b, a]

end SszArm.Emit.Bits
