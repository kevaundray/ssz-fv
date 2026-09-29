import SszArm.CodecDecodeBoundedActivation
import SszArm.CodecDecodeBoundedEntry
import SszArm.CodecDecodeBoundedReturn

namespace SszArm.Codec.Decode.Bounded

/-- Architectural invariant between the prologue and the restoring RET. The
saved fields describe actual memory, not promised future restoration. -/
structure Activation (initial current : ArmState) : Prop where
  stack : r (.GPR 31#5) current = bodySP initial
  saved : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 (bodySP initial + BitVec.ofNat 64 offset) current = r (.GPR reg) initial
  registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
    reg ∉ [19#5, 20#5, 21#5, 22#5, 30#5] → r (.GPR reg) current = r (.GPR reg) initial
  vectors : ∀ reg : BitVec 5, r (.SFP reg) current = r (.SFP reg) initial
  program : current.program = initial.program
  error : read_err current = .None

theorem activation_entered (s : ArmState) (base : BitVec 64)
    (low : 64 ≤ (r (.GPR 31#5) s).toNat) (error : read_err s = .None) :
    Activation s (tagRead (prologue s base) base) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tagRead, state_simp_rules]
  · intro reg offset member
    simpa only [tagRead, state_simp_rules] using prologue_saved s base low reg offset member
  · intro reg low high outside
    have nineteen : reg ≠ 19#5 := by
      intro same
      exact outside (by simp [same])
    have eight : reg ≠ 8#5 := by bv_omega
    have stack : reg ≠ 31#5 := by bv_omega
    simp [tagRead, state_simp_rules, nineteen, eight, prologue_register, stack]
  · intro reg
    simp [tagRead, state_simp_rules]
  · simp [tagRead, state_simp_rules]
  · simpa [tagRead, state_simp_rules] using error

/-- A readonly register-only phase transports saved memory directly. -/
theorem Activation.readonly {s t u : ArmState} (active : Activation s t)
    (memory : u.mem = t.mem) (stack : r (.GPR 31#5) u = r (.GPR 31#5) t)
    (registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
      reg ∉ [19#5, 20#5, 21#5, 22#5, 30#5] → r (.GPR reg) u = r (.GPR reg) t)
    (vectors : ∀ reg : BitVec 5, r (.SFP reg) u = r (.SFP reg) t)
    (program : u.program = t.program) (error : read_err u = read_err t) : Activation s u := by
  refine ⟨stack.trans active.stack, ?_, ?_, ?_, program.trans active.program,
    error.trans active.error⟩
  · intro reg offset member
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp memory]
    exact active.saved reg offset member
  · intro reg low high outside
    exact (registers reg low high outside).trans (active.registers reg low high outside)
  · intro reg
    exact (vectors reg).trans (active.vectors reg)

theorem Activation.restore {s t : ArmState} (active : Activation s t) :
    read_pc (restored t) = r (.GPR 30#5) s ∧ read_err (restored t) = .None ∧
    r (.GPR 31#5) (restored t) = r (.GPR 31#5) s ∧
    (∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
      r (.GPR reg) (restored t) = r (.GPR reg) s) ∧
    (∀ reg : BitVec 5, r (.SFP reg) (restored t) = r (.SFP reg) s) := by
  have lr := active.saved 30#5 0 (by simp [savedRegisters])
  have r19 := active.saved 19#5 40 (by simp [savedRegisters])
  have r20 := active.saved 20#5 32 (by simp [savedRegisters])
  have r21 := active.saved 21#5 24 (by simp [savedRegisters])
  have r22 := active.saved 22#5 16 (by simp [savedRegisters])
  simp only [BitVec.ofNat_zero, BitVec.add_zero] at lr
  refine ⟨?_, by simpa using active.error, ?_, ?_, ?_⟩
  · simpa only [restored_pc, active.stack] using lr
  · simp only [restored_sp, active.stack, bodySP, BitVec.sub_add_cancel]
  · intro reg low high
    by_cases h19 : reg = 19#5
    · subst reg; simpa [restored, state_simp_rules, active.stack] using r19
    by_cases h20 : reg = 20#5
    · subst reg; simpa [restored, state_simp_rules, active.stack] using r20
    by_cases h21 : reg = 21#5
    · subst reg; simpa [restored, state_simp_rules, active.stack] using r21
    by_cases h22 : reg = 22#5
    · subst reg; simpa [restored, state_simp_rules, active.stack] using r22
    by_cases h30 : reg = 30#5
    · subst reg; simpa [restored, state_simp_rules, active.stack] using lr
    have h31 : reg ≠ 31#5 := by bv_omega
    rw [restored_register t reg (by simp [h19, h20, h21, h22, h30, h31])]
    exact active.registers reg low high (by simp [h19, h20, h21, h22, h30])
  · intro reg
    exact (restored_vector t reg).trans (active.vectors reg)

end SszArm.Codec.Decode.Bounded
