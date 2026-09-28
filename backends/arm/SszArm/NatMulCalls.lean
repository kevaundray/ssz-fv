import SszArm.NatMulContract
import SszArm.MemsetProofs

namespace SszArm.NatMul

def wordOffset : BitVec 64 := 1544#64

def memsetOffset : BitVec 64 := 167060#64

structure JointCodeAt (s : ArmState) (base : BitVec 64) : Prop where
  body : CodeAt s base
  word : NatMulWord.CodeAt s (base + wordOffset)
  memset : SszArm.CodeAt s (base + memsetOffset) Memset.program

theorem JointCodeAt.transport {s t : ArmState} {base : BitVec 64}
    (code : JointCodeAt s base) (same : t.program = s.program) : JointCodeAt t base := by
  constructor
  · simpa only [CodeAt, same] using code.body
  · simpa only [NatMulWord.CodeAt, same] using code.word
  · simpa only [SszArm.CodeAt, same] using code.memset

def memsetCalled (s : ArmState) (base : BitVec 64) : ArmState :=
  w (.GPR 30#5) (base + 580#64) (w .PC (base + memsetOffset) s)

theorem memset_call (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 576#64) : stepi s = memsetCalled s base := by
  have fetched := code (576, 0x9400a295#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [exec_inst, memsetCalled, memsetOffset, state_simp_rules, bitvec_rules,
      minimal_theory, pc, BitVec.add_assoc]
  exact w_of_w_commute (by decide)

theorem tailbranch (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 260#64) :
    stepi s = w .PC (base + wordOffset) s := by
  have fetched := code (260, 0x14000141#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [exec_inst, wordOffset, state_simp_rules, bitvec_rules,
      minimal_theory, pc, BitVec.add_assoc]

theorem memset_call_run (s : ArmState) (base : BitVec 64)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 576#64)
    (physical : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64) :
    ∃ t, run (1 + Memset.fuel (r (.GPR 2#5) s).toNat) s = t ∧
      read_err t = .None ∧ read_pc t = base + 580#64 ∧
      t.program = s.program ∧
      (∀ f, Memset.Preserved f → r f t = r f (memsetCalled s base)) ∧
      (∀ a, t.mem a = Memset.image s.mem (r (.GPR 0#5) s)
        ((r (.GPR 1#5) s).setWidth 8) (r (.GPR 2#5) s).toNat a) := by
  let c := memsetCalled s base
  have fetched : run 1 s = c := by
    simpa only [run] using memset_call s base code.body error pc
  have cProgram : c.program = s.program := by simp [c, memsetCalled, state_simp_rules]
  have cCode := code.transport cProgram
  have correct := Memset.program_correct c (base + memsetOffset) cCode.memset
    (by simp [c, memsetCalled, state_simp_rules])
    (by simpa [c, memsetCalled, state_simp_rules] using error)
    (by simpa [c, memsetCalled, state_simp_rules] using physical)
  let t := run (Memset.fuel (r (.GPR 2#5) c).toNat) c
  refine ⟨t, ?_, correct.1, ?_, correct.2.2.2.1.trans cProgram, ?_, ?_⟩
  · rw [run_plus, fetched]
    change run _ c = run _ c
    have sameCount : r (.GPR 2#5) c = r (.GPR 2#5) s := by
      simp [c, memsetCalled, state_simp_rules]
    rw [sameCount]
  · have returned : read_pc t = r (.GPR 30#5) c := by
      with_unfolding_all exact correct.2.1
    exact returned.trans (by simp [c, memsetCalled, state_simp_rules])
  · exact correct.2.2.2.2.1
  · intro a
    have memory : t.mem a = Memset.image c.mem (r (.GPR 0#5) c)
        ((r (.GPR 1#5) c).setWidth 8) (r (.GPR 2#5) c).toNat a := by
      with_unfolding_all exact correct.2.2.2.2.2 a
    simpa (config := {decide := true}) only [c, memsetCalled, state_simp_rules] using memory

end SszArm.NatMul
