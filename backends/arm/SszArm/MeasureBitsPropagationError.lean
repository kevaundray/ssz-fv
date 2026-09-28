import SszArm.MeasureBitsPropagationCopy

namespace SszArm.Measure.Bits.Propagation

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

structure ErrorPost (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 4116#64
  program : t.program = s.program
  error : read_err t = .None
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 1#5, 2#5, 3#5, 4#5, 8#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  result : ResultAt (widthLoad t) (r (.GPR 19#5) s).toNat (.error (.arithmetic .scratchExhausted))
  tail : read_mem_bytes 4 (r (.GPR 19#5) s + 68#64) t =
    read_mem_bytes 4 (r (.GPR 31#5) s + 188#64) s
  frame : MemoryFrame [((r (.GPR 19#5) s).toNat, 72)] s t

theorem error_executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1928#64)
    (scratch : r (.GPR 23#5) s = r (.GPR 31#5) s + 120#64)
    (space : CopySpace s)
    (leading : r (.GPR 21#5) s = 1#64) (length : r (.GPR 20#5) s = 0#64)
    (status : (r (.GPR 22#5) s).setWidth 32 = 32768#32)
    (payload : ∀ index : Fin 6,
      widthLoad s ((r (.GPR 31#5) s).toNat + (136 + 8 * index.val)) 8 = some 0) :
    ∃ t, run (3 + (Memcpy.fuel 48 + 1) + 4) s = t ∧ ErrorPost s t base := by
  obtain ⟨m, copiedRun, copied⟩ := copy_executes s base code error aligned pc scratch space
  let t := Stage.finish.result m base
  have sp := copied.registers 31#5 (by decide)
  have output := copied.registers 19#5 (by decide)
  have mAligned : CheckSPAlignment m := by
    simpa only [CheckSPAlignment, state_simp_rules, sp] using aligned
  have finishRun : run 4 m = t := executes .finish m base (code.congr copied.program)
    copied.error mAligned copied.pc
  have physical : (r (.GPR 19#5) m).toNat + 72 ≤ 2^64 := by
    simpa only [output] using space.output
  refine ⟨t, by rw [run_plus, copiedRun, finishRun], ?_,
    (stage_program .finish m base).trans copied.program,
    (stage_error .finish m base).trans copied.error, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, Stage.result, state_simp_rules]
  · intro reg keep
    exact (stage_register .finish m base reg (by
      simp_all only [Stage.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or,
        not_false_eq_true])).trans
      (copied.registers reg (by
        simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]))
  · intro reg nonzero
    exact (stage_vector .finish m base reg).trans (copied.vectors reg nonzero)
  · rw [← output]
    apply finish_at m base physical
    · exact (copied.registers 21#5 (by decide)).trans leading
    · exact (copied.registers 20#5 (by decide)).trans length
    · rw [copied.registers 22#5 (by decide)]
      exact status
    · intro index
      rw [output, copied.payload (8 * index.val) 8 (by have := index.isLt; omega)]
      exact payload index
  · rw [← output, finish_tail m base physical, sp]
    apply copied.frame.read
    · have bound := space.scratch
      bv_omega
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      have separate := space.separate
      have bound := space.scratch
      dsimp
      bv_omega
  · have finishing := finish_frame m base physical
    intro address outside
    have apart := outside ((r (.GPR 19#5) s).toNat, 72) (by simp)
    have after : t.mem address = m.mem address := finishing address (by
      intro span member
      simp only [output, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> dsimp at apart ⊢ <;> omega)
    have before : m.mem address = s.mem address := copied.frame address (by
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      dsimp at apart ⊢
      omega)
    exact after.trans before

end SszArm.Measure.Bits.Propagation
