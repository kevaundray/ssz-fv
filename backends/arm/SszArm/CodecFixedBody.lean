import SszArm.CodecFixedObservations
import SszArm.CodecFixedSelected

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

/-- Physical caller context after the real prologue. Saved words are observed,
not assumed future returns; the prologue theorem constructs this invariant. -/
structure BodyContext (source current : ArmState) : Prop where
  saved : Saved source current
  registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
    reg ≠ 19#5 → reg ≠ 20#5 → reg ≠ 30#5 → r (.GPR reg) current = r (.GPR reg) source
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) source).setWidth 64

structure BodyOwned (source current : ArmState) (desc : Desc) : Prop where
  stack : isFixedStack desc ≤ (r (.GPR 31#5) source).toNat
  context : BodyContext source current
  descriptor : Storage.DescOwned (writes source desc) current (r (.GPR 0#5) current).toNat desc

structure BodyPost (source current final : ArmState) (desc : Desc) : Prop where
  returned : Delimited.Returned source final
  platform : r (.GPR 18#5) final = r (.GPR 18#5) source
  program : final.program = current.program
  result : r (.GPR 0#5) final = if SszNative.FixedSize.isFixed desc then 1#64 else 0#64
  frame : Delimited.MemoryFrame (writes source desc) current final

theorem BodyPost.to_post {source current final : ArmState} {desc : Desc}
    (post : BodyPost source current final desc)
    (program : current.program = source.program)
    (frame : Delimited.MemoryFrame (writes source desc) source current) : Post source final desc :=
  ⟨post.returned, post.platform, post.program.trans program, post.result, frame.trans post.frame⟩

theorem prologue_context (s : ArmState) (low : 32 ≤ (r (.GPR 31#5) s).toNat) :
    BodyContext s (prologue s) := by
  refine ⟨prologue_saved s low, ?_, ?_⟩
  · intro reg lower upper h19 h20 h30
    exact prologue_register s reg (by bv_omega)
  · intro reg lower upper
    simp only [prologue, block_vector]

theorem BodyContext.selected {source current : ArmState}
    (context : BodyContext source current) (tag : SszNative.Codec.DescTag) :
    BodyContext source (block (selectedOps tag) current) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(selected_register current tag 31#5).trans context.saved.sp, ?_, ?_, ?_⟩
    all_goals rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (selected_memory current tag))]
    · exact context.saved.link
    · exact context.saved.first
    · exact context.saved.second
  · intro reg lower upper h19 h20 h30
    exact (selected_register current tag reg).trans (context.registers reg lower upper h19 h20 h30)
  · intro reg lower upper
    rw [block_vector]
    exact context.vectors reg lower upper

theorem BodyContext.vector {source current : ArmState}
    (context : BodyContext source current) : BodyContext source (block vectorOps current) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(vector_register current 31#5 (by decide) (by decide)).trans context.saved.sp, ?_, ?_, ?_⟩
    all_goals rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (vector_memory current))]
    · exact context.saved.link
    · exact context.saved.first
    · exact context.saved.second
  · intro reg lower upper h19 h20 h30
    exact (vector_register current reg (by bv_omega) (by bv_omega)).trans
      (context.registers reg lower upper h19 h20 h30)
  · intro reg lower upper
    rw [block_vector]
    exact context.vectors reg lower upper

/-- The body continuation specification used under structural induction. -/
def BodyCorrect (desc : Desc) : Prop :=
  ∀ source current base, BodyOwned source current desc → CodeAt current base →
    read_err current = .None → CheckSPAlignment current →
    read_pc current = base + selectedEntry desc.tag →
    r (.GPR 8#5) current = tagWord desc.tag →
    ∃ fuel final, run fuel current = final ∧ BodyPost source current final desc

end SszArm.Codec.Fixed.IsFixed
