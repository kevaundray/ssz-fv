import SszArm.MeasureBitsPropagationFields
import SszArm.MeasureMemory

namespace SszArm.Measure.Bits.Propagation

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

structure CopySpace (s : ArmState) : Prop where
  output : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64
  scratch : (r (.GPR 31#5) s).toNat + 192 ≤ 2^64
  separate : (r (.GPR 19#5) s).toNat + 72 ≤ (r (.GPR 31#5) s).toNat + 120 ∨
    (r (.GPR 31#5) s).toNat + 192 ≤ (r (.GPR 19#5) s).toNat

structure Copied (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 1944#64
  program : t.program = s.program
  error : read_err t = .None
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 1#5, 2#5, 3#5, 4#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  payload : ∀ offset bytes, offset + bytes ≤ 48 →
    widthLoad t ((r (.GPR 19#5) s).toNat + (16 + offset)) bytes =
      widthLoad s ((r (.GPR 31#5) s).toNat + (136 + offset)) bytes
  frame : MemoryFrame [((r (.GPR 19#5) s).toNat + 16, 48)] s t

theorem copy_executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1928#64)
    (scratch : r (.GPR 23#5) s = r (.GPR 31#5) s + 120#64)
    (space : CopySpace s) :
    ∃ t, run (3 + (Memcpy.fuel 48 + 1)) s = t ∧ Copied s t base := by
  let p := Stage.prepare.result s base
  have prepareRun : run 3 s = p := executes .prepare s base code error aligned pc
  have destination : r (.GPR 0#5) p = r (.GPR 19#5) s + 16#64 := by
    simp [p, Stage.result, state_simp_rules]
  have source : r (.GPR 1#5) p = r (.GPR 31#5) s + 136#64 := by
    simp [p, Stage.result, state_simp_rules, scratch, BitVec.add_assoc]
  have count : r (.GPR 2#5) p = 48#64 := by simp [p, Stage.result, state_simp_rules]
  have countNat : (r (.GPR 2#5) p).toNat = 48 := by
    simpa only [count] using (show (48#64).toNat = 48 by decide)
  have destinationNat : (r (.GPR 0#5) p).toNat = (r (.GPR 19#5) s).toNat + 16 := by
    rw [destination]
    have := space.output
    bv_omega
  have sourceNat : (r (.GPR 1#5) p).toNat = (r (.GPR 31#5) s).toNat + 136 := by
    rw [source]
    have := space.scratch
    bv_omega
  have copyPost := Helpers.memcpy_correct p base (code.congr (stage_program .prepare s base))
    ((stage_error .prepare s base).trans error)
    (by simp [p, Stage.result, state_simp_rules])
    (by rw [destinationNat, countNat]; have := space.output; omega)
    (by rw [sourceNat, countNat]; have := space.scratch; omega)
    (by
      unfold Memcpy.Disjoint
      rw [destinationNat, sourceNat, countNat]
      have := space.separate
      omega)
  let t := run (Memcpy.fuel 48 + 1) p
  have post : Helpers.CopyPost p t base := by
    simpa only [countNat] using copyPost
  refine ⟨t, by rw [run_plus, prepareRun], post.pc,
    post.program.trans (stage_program .prepare s base), post.error, ?_, ?_, ?_, ?_⟩
  · intro reg keep
    have untouched : reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] :=
      fun member => keep (List.mem_cons.mpr (Or.inr member))
    have preparationKeep : reg ∉ Stage.prepare.clobbers := by
      intro member
      apply keep
      simp only [Stage.clobbers, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same <;> simp [same]
    exact (post.registers reg untouched).trans (stage_register .prepare s base reg preparationKeep)
  · intro reg nonzero
    exact (post.vectors reg nonzero).trans (stage_vector .prepare s base reg)
  · intro offset bytes within
    have copied := post.copied offset bytes (by simpa only [countNat] using within)
    have memory : p.mem = s.mem := prepare_memory s base
    simpa only [destinationNat, sourceNat, Nat.add_assoc,
      Emit.load_eq_of_mem_eq memory] using copied
  · intro address outside
    have unchanged := post.frame address (by
      simpa only [destinationNat, countNat] using outside)
    exact unchanged.trans (congrFun (prepare_memory s base) address)

end SszArm.Measure.Bits.Propagation
