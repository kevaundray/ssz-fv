import SszArm.MeasureBitsReturnedErrorRun

namespace SszArm.Measure.Bits

open UintCodec (widthLoad)
open Propagation

theorem returned_error_executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1916#64)
    (scratch : r (.GPR 23#5) s = r (.GPR 31#5) s + 120#64)
    (space : CopySpace s)
    (input : SszNative.NatArithmetic.errorAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 120) .scratchExhausted) :
    ∃ t, run (3 + (3 + (Memcpy.fuel 48 + 1) + 4)) s = t ∧
      ReturnedPost s t base (.error (.arithmetic .scratchExhausted))
        [((r (.GPR 19#5) s).toNat, 72)] := by
  obtain ⟨leading, length, word0, word1, word2, word3, word4, word5, status⟩ := input
  have first : read_mem_bytes 8 (r (.GPR 31#5) s + 120#64) s = 1#64 :=
    BitVector.read_of_observe_offset s (r (.GPR 31#5) s) 120 8 1#64 leading
  have second : read_mem_bytes 8 (r (.GPR 31#5) s + 128#64) s = 0#64 :=
    BitVector.read_of_observe_offset s (r (.GPR 31#5) s) 128 8 0#64
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, (show (0#64).toNat = 0 by decide)] using length)
  have flag : read_mem_bytes 4 (r (.GPR 31#5) s + 184#64) s = 32768#32 :=
    BitVector.read_of_observe_offset s (r (.GPR 31#5) s) 184 4 32768#32
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, (show (32768#32).toNat = 32768 by decide)] using status)
  let p := Stage.returned.result s base
  have before : run 3 s = p := executes .returned s base code error aligned pc
  have pSpace : CopySpace p := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [p, Stage.result, state_simp_rules] using space.output
    · simpa [p, Stage.result, state_simp_rules] using space.scratch
    · simpa [p, Stage.result, state_simp_rules] using space.separate
  have pAligned : CheckSPAlignment p := by
    simpa only [p, CheckSPAlignment, state_simp_rules, stage_sp] using aligned
  obtain ⟨t, after, post⟩ := error_executes p base (code.congr (stage_program .returned s base))
    ((stage_error .returned s base).trans error) pAligned
    (by simp [p, Stage.result, state_simp_rules, flag])
    (by simpa [p, Stage.result, state_simp_rules] using scratch)
    pSpace
    (by simp [p, Stage.result, state_simp_rules, first])
    (by simp [p, Stage.result, state_simp_rules, second])
    (by simp [p, Stage.result, state_simp_rules, flag])
    (by
      intro index
      rw [stage_sp .returned s base, Emit.load_eq_of_mem_eq (returned_memory s base)]
      have bound := index.isLt
      have positions : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨
          index.val = 3 ∨ index.val = 4 ∨ index.val = 5 := by omega
      rcases positions with position | position | position | position | position | position
      all_goals simp only [position, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul,
        Nat.reduceAdd, Nat.add_assoc] at word0 word1 word2 word3 word4 word5 ⊢
      · exact word0
      · exact word1
      · exact word2
      · exact word3
      · exact word4
      · exact word5)
  refine ⟨t, returned_error_run 3 (3 + (Memcpy.fuel 48 + 1) + 4) s p t before after,
    returned_error_post s p t base post
    (stage_program .returned s base) (returned_memory s base)
    (stage_register .returned s base 19#5 (by decide)) (stage_sp .returned s base) ?_ ?_⟩
  · intro reg member
    apply stage_register .returned s base reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro reg low high
    exact congrArg (fun value : BitVec 128 => value.setWidth 64)
      (stage_vector .returned s base reg)

end SszArm.Measure.Bits
