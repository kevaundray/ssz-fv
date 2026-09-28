import SszArm.MeasureBitsListWidthFirst
import SszArm.MeasureBitsConstructor
import SszArm.MeasureBitListSpace

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (MemoryFrame)

theorem width_executes (schema : Schema) (s u : ArmState) (args : Args) (bits : Packed)
    (actual : NatOperand) (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (code : CodeAt u base) (error : read_err u = .None) (aligned : CheckSPAlignment u)
    (pc : read_pc u = base + 1852#64) :
    ∃ fuel t, run fuel u = t ∧ Produced s t args schema.descriptor (.bits bits) base := by
  have stackLow : 16 ≤ (r (.GPR 31#5) u).toNat := by
    have low := owned.stackLow
    rw [pre.core.stack, Args.bodySP]
    bv_omega
  have firstRun := Width.executes u base code error aligned pc stackLow
  have wAligned : CheckSPAlignment (Width.result u base) := by
    simpa only [CheckSPAlignment, state_simp_rules, Width.result_register u base 31#5 (by decide)] using aligned
  obtain ⟨fuel, t, secondRun, post⟩ := Constructor.executes (Width.result u base) base
    (width_space owned pre checked base) (code.congr (Width.result_program u base))
    ((Width.result_error u base).trans error) wAligned (Width.result_pc u base)
  have regs := width_registers pre base
  have arena := width_arena owned pre base
  have baseWord : NatFromU128.addressWord (Width.result u base) = read_mem_bytes 8 args.arena s := by
    apply BitVec.eq_of_toNat_eq
    exact congrArg SszNative.Delimited.ArenaState.base arena
  have capacityWord : NatFromU128.capacityWord (Width.result u base) =
      read_mem_bytes 8 (args.arena + 8#64) s := by
    apply BitVec.eq_of_toNat_eq
    exact congrArg SszNative.Delimited.ArenaState.capacity arena
  have firstWritten := width_first_written owned pre checked base post.frame
    (prefix_width_written owned pre base)
  refine ⟨6 + (6 + (Width.finishOps (Width.carry u)).length) + fuel, t,
    by rw [run_plus, firstRun, secondRun], post.pc,
    post.program.trans ((Width.result_program u base).trans pre.program), post.error,
    post.stack.trans regs.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [regs.2.1, Constructor.result, width_outcome owned pre base,
      width_model pre checked] using post.result
  · simpa only [regs.2.2.1, width_outcome owned pre base,
      width_model pre checked] using post.cursor
  · simpa only [regs.2.2.1, baseWord, capacityWord] using post.header
  · intro call member
    simp only [width_model pre checked, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact firstWritten
    · simpa only [width_outcome owned pre base] using post.written
  · have entered : MemoryFrame (bodyWrites args (outcome s args schema.descriptor (.bits bits))) s u := by
      apply pre.frame.weaken
      intro span member
      simp only [prefixWrites, List.mem_append, List.mem_singleton] at member
      rcases member with rfl | allocated
      · simp [bodyWrites, bodyStackWrites]
      · exact List.mem_append.mpr (Or.inr (count_writes_subset schema s args bits span allocated))
    have widthFrame : MemoryFrame (bodyWrites args (outcome s args schema.descriptor (.bits bits))) u (Width.result u base) := by
      apply (Width.result_frame u base stackLow).weaken
      intro span member
      have within := lowering_subset_body args (outcome s args schema.descriptor (.bits bits))
        u owned.stackLow pre.core.stack span member
      simp only [bodyWrites, List.mem_append, within, true_or]
    exact (entered.trans widthFrame).trans ((width_constructor_cover owned pre checked base).frame post.frame)
  · intro reg member
    have unchanged : reg ∉ [0#5, 2#5, 3#5, 4#5, 8#5, 9#5, 23#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (post.registers reg member).trans
      ((Width.result_register u base reg unchanged).trans (pre.registers reg member))
  · intro reg low high
    exact (post.vectors reg low high).trans (congrArg (fun wordValue : BitVec 128 => wordValue.setWidth 64)
      ((Width.result_vector u base reg).trans (pre.vectors reg)))

end SszArm.Measure.Bits.List
