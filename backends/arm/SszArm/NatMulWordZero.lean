import SszArm.NatMulWordReturnValues
import SszArm.WordNormalize

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected Returned)

def zeroDispatch (s : ArmState) (base : BitVec 64) : ArmState :=
  block base [.p0, .p4, .p8] s

theorem zero_dispatch_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) (factor : r (.GPR 3#5) s = 0#64) :
    run 3 s = zeroDispatch s base ∧ read_pc (zeroDispatch s base) = base + 12#64 := by
  have hpc : r .PC s = base := pc
  have nonone : ¬(AddWithCarry (r (.GPR 3#5) s) (~~~1#64) 1#1).2.z = 1#1 := by
    rw [Udivti3.cmp_zero, factor]
    decide
  constructor
  · apply block_run base [.p0, .p4, .p8] s code error aligned
    simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, hpc, factor, nonone, BitVec.add_assoc]
  · simp [zeroDispatch, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, factor, nonone]

@[simp] theorem zero_dispatch_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (zeroDispatch s base) = r (.GPR reg) s := by
  simp [zeroDispatch, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem zero_dispatch_memory (s : ArmState) (base : BitVec 64) :
    (zeroDispatch s base).mem = s.mem := by
  simp [zeroDispatch, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem zero_correct (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (owned : Owned s operand 0#64) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ t, run 25 s = t ∧ Post s t operand 0#64 := by
  let u := zeroDispatch s base
  have dispatch := zero_dispatch_run s base code error aligned
    (by simpa [entry] using pc) owned.factorRegister
  have uOwned : ReturnOwned u := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [u, zero_dispatch_register] using owned.return_owned.stack
    · simpa only [u, zero_dispatch_register] using owned.return_owned.output
    · simpa only [u, zero_dispatch_register] using owned.return_owned.separate
  have uCode : CodeAt u base := by
    simpa only [u, zeroDispatch, CodeAt, block_program] using code
  have uError : read_err u = .None := (block_error _ _ _).trans error
  have uAligned : CheckSPAlignment u := block_aligned _ _ _ aligned
  have body := value_run_contract .zero u base uCode uError uAligned
    (by simpa only [valueStart] using dispatch.2) uOwned (.small 0#64) rfl rfl trivial trivial
  let t := valueResult .zero base u
  have output : r (.GPR 0#5) u = r (.GPR 0#5) s := zero_dispatch_register _ _ _
  have sp : r (.GPR 31#5) u = r (.GPR 31#5) s := zero_dispatch_register _ _ _
  have model : outcome s operand 0#64 = SszNative.NatArithmetic.unchanged (arenaOf s).used (.ok (.small 0)) :=
    SszNative.NatMul.runWord_zero _ _ _ _
  have frame : MemoryFrame (writesFor s (outcome s operand 0#64)) s t := by
    intro a outside
    have low := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [writesFor, model, localWrites,
      SszNative.NatArithmetic.unchanged])
    have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [writesFor, model, localWrites,
      SszNative.NatArithmetic.unchanged])
    have stack := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp [writesFor, model, localWrites,
      SszNative.NatArithmetic.unchanged])
    have preserved := body.2.2.2 a (by
      intro span member
      simp only [valueWrites, NatAdd.valueWrites, output, sp, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact low
      · exact status
      · have := owned.stackBound
        omega)
    exact preserved.trans (congrFun (zero_dispatch_memory s base) a)
  have arenaProtected : Protected (writesFor s (outcome s operand 0#64))
      (r (.GPR 4#5) s).toNat 24 := by
    simpa only [writesFor, model, SszNative.NatArithmetic.unchanged] using owned.arenaLocal
  have arena16 : (r (.GPR 4#5) s + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by
    have := owned.arenaBound
    bv_omega
  have arena8 : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by
    have := owned.arenaBound
    bv_omega
  have cursor := frame.read (r (.GPR 4#5) s + 16#64) 8
    (by rw [arena16]; exact owned.arenaBound) (by rw [arena16]; exact arenaProtected.subspan 16 8 (by decide))
  refine ⟨t, ?_, ?_⟩
  · change run (3 + 22) s = t
    rw [run_plus, dispatch.1]
    exact body.1
  · constructor
    · refine ⟨?_, body.2.1.error, ?_, ?_, ?_⟩
      · exact body.2.1.pc.trans (zero_dispatch_register _ _ _)
      · exact body.2.1.sp.trans sp
      · intro reg low high
        exact (body.2.1.registers reg low high).trans (zero_dispatch_register _ _ _)
      · intro reg low high
        rw [body.2.1.vectors reg low high]
        simp [u, zeroDispatch, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]
    · have result := body.2.2.1
      simp only [model, SszNative.NatArithmetic.unchanged, output, t] at result ⊢
      arm_word_nf at result ⊢
      exact result
    · intro reservation allocation
      simp [model, SszNative.NatArithmetic.unchanged] at allocation
    · rw [cursor, model]
      rfl
    · exact frame
    · exact NatAdd.operand_preserved frame operand owned.operandAt owned.inputOwned
    · exact frame.read _ 8 (by have := owned.arenaBound; omega)
        (by simpa only [Nat.add_zero] using arenaProtected.subspan 0 8 (by decide))
    · exact frame.read _ 8 (by rw [arena8]; have := owned.arenaBound; omega)
        (by rw [arena8]; exact arenaProtected.subspan 8 8 (by decide))

end SszArm.NatMulWord
