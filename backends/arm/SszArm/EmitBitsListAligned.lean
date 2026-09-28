import SszArm.EmitBitsTailState
import SszArm.EmitBitsCompose

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open UintCodec (widthLoad)

theorem list_aligned_suffix (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat) (kind : IsList desc)
    (owned : Owned s args desc (.bits bits) size) (work : WorkRegisters s args .list bits)
    (byteAligned : bits.count.toNat % 8 = 0)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad s (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 652#64) :
    ∃ t, run 14 s = t ∧ Produced s t args desc (.bits bits) size base := by
  let a := listBranched s base false
  let b := delimiterOne a
  let c := tailGuarded .listCapacity b
  let d := byteStored c
  have sizeEq := list_size kind owned.expected
  have aRun : run 1 s = a := by
    simpa only [byteAligned, ne_eq, not_true_eq_false, decide_false] using
      list_branch_run s base args bits work code error aligned pc
  have aPC : read_pc a = base + 1484#64 := by simp [a, listBranched, state_simp_rules]
  have aCode : CodeAt a base := by simpa [a, listBranched, CodeAt, state_simp_rules] using code
  have aError : read_err a = .None := by simpa [a, listBranched, state_simp_rules] using error
  have aAligned : CheckSPAlignment a := by simpa [a, listBranched, state_simp_rules] using aligned
  have bRun := delimiter_one_run a base aCode aError aAligned aPC
  have bMemory : b.mem = s.mem := by simp [b, a, delimiterOne, listBranched, Activation.put, Activation.next, state_simp_rules]
  have bRegisters (reg : BitVec 5) (other : reg ≠ 8#5) : r (.GPR reg) b = r (.GPR reg) s := by
    simp [b, a, delimiterOne, listBranched, Activation.put, Activation.next, state_simp_rules, other]
  have bWork : WorkRegisters b args .list bits := work.of_memory owned bMemory (by
    intro reg untouched
    apply bRegisters reg
    simp_all)
  have bInput : Owned b args desc (.bits bits) size := owned.of_mem_eq bMemory
  have bPC : read_pc b = base + 1488#64 := by
    change r .PC a = _ at aPC
    simp [b, delimiterOne, Activation.put, Activation.next, state_simp_rules, aPC, BitVec.add_assoc]
  have bCode : CodeAt b base := by simpa [b, delimiterOne, Activation.put, Activation.next, CodeAt, state_simp_rules] using aCode
  have bError : read_err b = .None := by simpa [b, delimiterOne, Activation.put, Activation.next, state_simp_rules] using aError
  have bAligned := aligned_of_stack aligned (bRegisters 31#5 (by decide))
  have good : TailGuard.good .listCapacity b := by
    change (r (.GPR 23#5) b).toNat < (r (.GPR 21#5) b).toNat
    rw [bWork.full, bWork.capacity]
    exact (list_guards kind bInput).1
  have cRun := tail_guard_run .listCapacity b base bCode bError bAligned bPC
  have cPC : read_pc c = base + 1496#64 := by
    rw [tailGuarded_pc .listCapacity b good, bPC]
    simp [BitVec.add_assoc]
  have cMemory : c.mem = s.mem := (tailGuarded_memory .listCapacity b).trans bMemory
  have cInput : Owned c args desc (.bits bits) size := owned.of_mem_eq cMemory
  have cRegisters (reg : BitVec 5) (other : reg ≠ 8#5) : r (.GPR reg) c = r (.GPR reg) s :=
    (tailGuarded_register .listCapacity b reg).trans (bRegisters reg other)
  have cWork : WorkRegisters c args .list bits := work.of_memory owned cMemory (by
    intro reg untouched
    apply cRegisters reg
    simp_all)
  have cCode : CodeAt c base := by simpa only [c, CodeAt, tailGuarded_program] using bCode
  have cError : read_err c = .None := (tailGuarded_error .listCapacity b).trans bError
  have cAligned := aligned_of_stack aligned (cRegisters 31#5 (by decide))
  have inside : (r (.GPR 23#5) c).toNat < size := by rw [cWork.full, sizeEq]; omega
  have dRun := store_run .list base cInput cWork.output cWork.stack inside cCode cError cAligned cPC
  have dFrame := byteStored_frame cInput cWork.output cWork.stack inside
  have dInput := cInput.of_body_frame dFrame
  have dWork := cWork.of_body_frame cInput dFrame (fun reg _ => byteStored_register c reg)
  have dCode : CodeAt d base := by simpa only [d, CodeAt, byteStored_program] using cCode
  have dError : read_err d = .None := (byteStored_error c).trans cError
  have dAligned := aligned_of_stack cAligned (byteStored_register c 31#5)
  have dPC : read_pc d = base + 1524#64 := by rw [byteStored_pc, cPC]; simp [BitVec.add_assoc]
  have delimiter : (r (.GPR 8#5) c).setWidth 8 = 1#8 := by
    simp [c, tailGuarded_register, b, delimiterOne, Activation.put, Activation.next, state_simp_rules]
  have output : SszNative.ByteView.BytesAt (widthLoad d) args.output.toNat
      (SszNative.Serialize.emit desc (.bits bits)) := by
    rw [list_emit desc bits kind]
    apply delimited_at
    · intro index before
      rw [byteStored_prefix cInput cWork.output cWork.stack inside index (by rwa [cWork.full]),
        load_eq_of_mem_eq cMemory]
      exact copiedPrefix index before
    · have tail := byteStored_tail cInput cWork.output inside
      rw [cWork.full, delimiter] at tail
      simpa only [d, byteAligned, if_true, BitVec.toNat_ofNat, UInt8.toNat_ofNat] using tail
  have count : r (.GPR 23#5) d + 1#64 = BitVec.ofNat 64 size := by
    have actualFull : (r (.GPR 23#5) d).toNat = bits.count.toNat / 8 := dWork.full
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, actualFull,
      Nat.mod_eq_of_lt (show 1 < 2^64 by decide)]
    rw [← sizeEq]
  have finishRun := finish_run .list d base args size dCode dError dAligned dPC dWork.result count
  have post := finished_post .list d base args desc bits size dInput dError dWork.result dWork.stack output
  refine ⟨finished .list d base args size, ?_, ?_⟩
  · change run (1 + (1 + (2 + (7 + 3)))) s = _
    rw [run_plus, aRun, run_plus, bRun, run_plus, cRun, run_plus, dRun]
    exact finishRun
  · apply produced_prepend post
    · simpa [d, c, b, a, delimiterOne, listBranched, Activation.put, Activation.next, state_simp_rules] using
        (byteStored_program c).trans ((tailGuarded_program .listCapacity b).trans
          (show b.program = s.program by simp [b, a, delimiterOne, listBranched, Activation.put, Activation.next, state_simp_rules]))
    · intro address outside
      exact (dFrame address outside).trans (congrFun cMemory address)
    · intro reg member
      have other : reg ≠ 8#5 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      exact (byteStored_register c reg).trans (cRegisters reg other)
    · intro reg low high
      simp [d, c, b, a, byteStored_vector, tailGuarded_vector, delimiterOne, listBranched,
        Activation.put, Activation.next, state_simp_rules]

end SszArm.Emit.Bits
