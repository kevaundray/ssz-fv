import SszArm.EmitBitsPayload
import SszArm.EmitBitsStoredSuffix

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open UintCodec (widthLoad)

theorem list_tail_suffix (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat) (kind : IsList desc)
    (owned : Owned s args desc (.bits bits) size) (work : WorkRegisters s args .list bits)
    (hasTail : bits.count.toNat % 8 ≠ 0)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad s (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 652#64) :
    ∃ t, run 34 s = t ∧ Produced s t args desc (.bits bits) size base := by
  let a := listBranched s base true
  let b := tailGuarded .listBacking a
  have bitsKind : IsBits desc := by cases desc <;> cases kind <;> trivial
  have pathEq : pathOf desc = .list := by cases desc <;> cases kind <;> rfl
  have sizeEq := list_size kind owned.expected
  have backing := (backing_guards bits).2.2 hasTail
  have live : bits.count.toNat / 8 < size := by omega
  have aRun : run 1 s = a := by
    simpa only [decide_eq_true hasTail] using list_branch_run s base args bits work code error aligned pc
  have aPC : read_pc a = base + 656#64 := by simp [a, listBranched, state_simp_rules]
  have aMemory : a.mem = s.mem := by simp [a, listBranched, state_simp_rules]
  have aRegisters (reg : BitVec 5) : r (.GPR reg) a = r (.GPR reg) s := by simp [a, listBranched, state_simp_rules]
  have aInput : Owned a args desc (.bits bits) size := owned.of_mem_eq aMemory
  have aWork := work.of_memory owned aMemory (fun reg _ => aRegisters reg)
  have aCode : CodeAt a base := by simpa [a, listBranched, CodeAt, state_simp_rules] using code
  have aError : read_err a = .None := by simpa [a, listBranched, state_simp_rules] using error
  have aAligned := aligned_of_stack aligned (aRegisters 31#5)
  have good : TailGuard.good .listBacking a := by
    change (r (.GPR 23#5) a).toNat < (r (.GPR 24#5) a).toNat
    rw [aWork.full, aWork.backing, backing]
    omega
  have bRun := tail_guard_run .listBacking a base aCode aError aAligned aPC
  have bPC : read_pc b = base + 664#64 := by
    rw [tailGuarded_pc .listBacking a good, aPC]
    simp [BitVec.add_assoc]
  have bMemory : b.mem = s.mem := (tailGuarded_memory .listBacking a).trans aMemory
  have bRegisters (reg : BitVec 5) : r (.GPR reg) b = r (.GPR reg) s :=
    (tailGuarded_register .listBacking a reg).trans (aRegisters reg)
  have bInput : Owned b args desc (.bits bits) size := owned.of_mem_eq bMemory
  have bWork := work.of_memory owned bMemory (fun reg _ => bRegisters reg)
  have bCode : CodeAt b base := by simpa only [b, CodeAt, tailGuarded_program] using aCode
  have bError : read_err b = .None := (tailGuarded_error .listBacking a).trans aError
  have bAligned := aligned_of_stack aligned (bRegisters 31#5)
  obtain ⟨u, payloadRun, payload⟩ := payload_run .list b base args desc bits size bitsKind
    bInput bWork hasTail bCode bError bAligned bPC
  let v := maskResult .delimiter u
  let w := tailGuarded .listCapacity v
  have uCode : CodeAt u base := by simpa only [CodeAt, payload.program] using bCode
  have uAligned := aligned_of_stack aligned (payload.work.stack.trans work.stack.symm)
  have vRun := mask_run .delimiter u base uCode payload.error uAligned payload.pc
  change run 4 u = v at vRun
  have vPC : read_pc v = base + 1488#64 := by
    rw [delimiter_pc, payload.pc]
    simp [Path.maskEnd, BitVec.add_assoc]
  have vInput : Owned v args desc (.bits bits) size := payload.owned.of_mem_eq (maskResult_memory .delimiter u)
  have vWork := payload.work.of_memory payload.owned (maskResult_memory .delimiter u)
    (maskResult_register .delimiter u)
  have vCode : CodeAt v base := by simpa only [v, CodeAt, maskResult_program] using uCode
  have vError : read_err v = .None := (maskResult_error .delimiter u).trans payload.error
  have vAligned := aligned_of_stack uAligned (maskResult_register .delimiter u 31#5 (by decide))
  have delimiter : (r (.GPR 8#5) v).setWidth 8 = (tailByte .list bits).toBitVec := by
    have remainder := payload.work.remainder rfl
    rw [delimiter_byte u (by rw [remainder]; omega), payload.byte, remainder]
    have encoded := delimiterByte_eq bits.bytes[bits.count.toNat / 8]! (bits.count.toNat % 8) (by omega)
    rw [delimiterByte, maskByte_eq _ _ (by omega)] at encoded
    simpa only [tailByte, hasTail, if_neg, if_false] using encoded
  have capacityGood : TailGuard.good .listCapacity v := by
    change (r (.GPR 23#5) v).toNat < (r (.GPR 21#5) v).toNat
    rw [vWork.full, vWork.capacity]
    exact (list_guards kind vInput).1
  have wRun := tail_guard_run .listCapacity v base vCode vError vAligned vPC
  have wPC : read_pc w = base + 1496#64 := by
    rw [tailGuarded_pc .listCapacity v capacityGood, vPC]
    simp [BitVec.add_assoc]
  have wMemory : w.mem = u.mem := (tailGuarded_memory .listCapacity v).trans (maskResult_memory .delimiter u)
  have wInput : Owned w args desc (.bits bits) size := payload.owned.of_mem_eq wMemory
  have wWork := vWork.of_memory vInput (tailGuarded_memory .listCapacity v)
    (fun reg _ => tailGuarded_register .listCapacity v reg)
  have wCode : CodeAt w base := by simpa only [w, CodeAt, tailGuarded_program] using vCode
  have wError : read_err w = .None := (tailGuarded_error .listCapacity v).trans vError
  have wAligned := aligned_of_stack vAligned (tailGuarded_register .listCapacity v 31#5)
  have wByte : (r (.GPR 8#5) w).setWidth 8 = (tailByte (pathOf desc) bits).toBitVec := by
    rw [tailGuarded_register, pathEq]
    exact delimiter
  have wPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad w (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat := by
    intro index before
    rw [load_eq_of_mem_eq wMemory, payload.output index before, load_eq_of_mem_eq bMemory]
    exact copiedPrefix index before
  obtain ⟨t, storedRun, post⟩ := stored_suffix w base args desc bits size bitsKind wInput
    (by simpa only [pathEq] using wWork) live wByte wPrefix wCode wError wAligned
    (by simpa only [pathEq, Path.storeStart] using wPC)
  refine ⟨t, ?_, ?_⟩
  · change run (1 + (2 + (15 + (4 + (2 + 10))))) s = _
    rw [run_plus, aRun, run_plus, bRun, run_plus, payloadRun, run_plus, vRun, run_plus, wRun]
    simpa only [pathEq, Path.finish, Finish.ops, List.length_cons, List.length_nil] using storedRun
  · apply produced_prepend post
    · exact (tailGuarded_program .listCapacity v).trans ((maskResult_program .delimiter u).trans
        (payload.program.trans (by simp [b, a, listBranched, state_simp_rules])))
    · intro address outside
      rw [wMemory]
      exact (payload.frame address outside).trans (congrFun bMemory address)
    · intro reg member
      have untouched : reg ∉ [8#5, 9#5, 10#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      rw [tailGuarded_register, maskResult_register .delimiter u reg untouched,
        payload.registers reg untouched, bRegisters reg]
    · intro reg low high
      rw [tailGuarded_vector, maskResult_vector, payload.vectors]
      simp [b, a, listBranched, state_simp_rules]

end SszArm.Emit.Bits
