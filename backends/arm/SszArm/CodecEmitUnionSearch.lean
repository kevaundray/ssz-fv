import SszArm.CodecEmitUnionScanOwnership
import SszCodecMeasureOrder

namespace SszArm.Codec.Emit.Union.Scan

open SszNative (NatOperand)
open SszNative.Codec (Desc)

structure Selected (s t : ArmState) (bias : BitVec 64) (chosen : Desc) : Prop where
  pc : read_pc t = bias + 2296452#64
  error : read_err t = .None
  program : t.program = s.program
  stack : r (.GPR 31#5) t = r (.GPR 31#5) s
  preserved : ∀ reg : BitVec 5, reg ∈ [18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 28#5, 29#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  frame : Delimited.MemoryFrame (scanWrites s) s t
  descriptor : ∃ pointer, read_mem_bytes 8 (r (.GPR 26#5) t) t = BitVec.ofNat 64 pointer ∧
    Storage.DescOwned (scanWrites s) t pointer chosen

/-- Actual first-match search, including duplicate and noncanonical selectors.
The finite list induction executes each real compare call and stops at the
first numerical equality. The sole success premise is the measured-plan option
lookup, not a future helper execution or a schema-validation assumption. -/
theorem search_correct (s : ArmState) (bias : BitVec 64) (address : Nat)
    (variants : List (NatOperand × Desc)) (selector : NatOperand) (chosen : Desc)
    (ready : Ready s address variants selector)
    (selected : SszNative.CodecMeasure.option variants selector = .ok chosen)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = bias + 2296416#64) :
    ∃ fuel t, run fuel s = t ∧ Selected s t bias chosen := by
  induction variants generalizing s address with
  | nil => cases selected
  | cons variant rest ih =>
    rcases variant with ⟨key, desc⟩
    obtain ⟨fuel, middle, execution, round⟩ :=
      ready_round s bias address key desc rest selector ready code error aligned pc
    by_cases same : key.value = selector.value
    · have identical : desc = chosen := by
        simpa only [SszNative.CodecMeasure.option, same, ↓reduceIte, Except.ok.injEq] using selected
      subst chosen
      have stored := Storage.Image.preserved (Storage.variantEntries address ((key, desc) :: rest))
        round.frame ready.variants
      obtain ⟨pointer, pointerAt, descriptorAt⟩ := Storage.variant_child stored
      have pointerBound : pointer < 2 ^ 64 := by
        have physical := Storage.desc_physical (Storage.desc_at descriptorAt)
        have := physical.2.2.1
        omega
      refine ⟨fuel, middle, execution, ?_⟩
      refine ⟨by simpa only [same, ↓reduceIte] using round.pc,
        round.error, round.program, round.stack, round.preserved, round.vectors, round.frame,
        pointer, ?_, descriptorAt⟩
      rw [round.cursor, ready.cursor, BitVec.sub_add_cancel]
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using Storage.word_read pointerAt
    · have remaining : SszNative.CodecMeasure.option rest selector = .ok chosen := by
        simpa only [SszNative.CodecMeasure.option, same, ↓reduceIte] using selected
      have nextReady := ready_tail ready round
      have nextAligned : CheckSPAlignment middle := by
        simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, round.stack] using aligned
      have nextPC : read_pc middle = bias + 2296416#64 := by
        simpa only [same, ↓reduceIte] using round.pc
      obtain ⟨tailFuel, final, tailExecution, tailPost⟩ := ih middle (address + 24)
        nextReady remaining (code.congr round.program) round.error nextAligned nextPC
      refine ⟨fuel + tailFuel, final, ?_, ?_⟩
      · rw [run_plus, execution, tailExecution]
      · refine ⟨tailPost.pc, tailPost.error, tailPost.program.trans round.program,
          tailPost.stack.trans round.stack, ?_, ?_, ?_, ?_⟩
        · intro reg member
          exact (tailPost.preserved reg member).trans (round.preserved reg member)
        · intro reg
          exact (tailPost.vectors reg).trans (round.vectors reg)
        · apply round.frame.trans
          simpa only [scanWrites, round.stack] using tailPost.frame
        · obtain ⟨pointer, pointerAt, descriptorAt⟩ := tailPost.descriptor
          exact ⟨pointer, pointerAt, by simpa only [scanWrites, round.stack] using descriptorAt⟩

end SszArm.Codec.Emit.Union.Scan
