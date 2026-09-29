import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

theorem vector_body_correct (child : Desc) (count : SszNative.NatOperand)
    (induction : BodyCorrect child) : BodyCorrect (.vector child count) := by
  intro source current base owned code error aligned pc loaded
  obtain ⟨pointer, pointerAt, childOwned⟩ := Storage.vector_child owned.descriptor
  have pointerRead := Storage.word_offset (r (.GPR 0#5) current) 24 pointerAt
  have pointerSmall : pointer < 2^64 := by
    rw [← pointerRead]
    exact BitVec.toNat_lt _
  have pointerNat : (BitVec.ofNat 64 pointer).toNat = pointer := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerSmall]
  have pointerBits : read_mem_bytes 8 (r (.GPR 0#5) current + 24#64) current =
      BitVec.ofNat 64 pointer := by
    apply BitVec.eq_of_toNat_eq
    simpa only [pointerNat] using pointerRead
  have childInput : Storage.DescAt current (BitVec.ofNat 64 pointer).toNat child := by
    rw [pointerNat]
    exact childOwned.at
  have childTag := desc_tag current (BitVec.ofNat 64 pointer) child childInput
  let q := block vectorOps current
  have qRun : run 4 current = q :=
    vector_run current base (BitVec.ofNat 64 pointer) child.tag code error aligned pc pointerBits childTag
  have args := vector_arguments current (BitVec.ofNat 64 pointer) child.tag pointerBits childTag
  have qPC : read_pc q = base + selectedEntry child.tag :=
    vector_pc current base (BitVec.ofNat 64 pointer) child.tag pc pointerBits childTag
  have qFrame : Delimited.MemoryFrame (writes source child) current q := by
    intro address outside
    rw [show q.mem = current.mem from vector_memory current]
  have keptChild : Storage.DescOwned (writes source child) q pointer child :=
    Storage.desc_preserved childOwned qFrame
  have qOwned : BodyOwned source q child := by
    refine ⟨owned.stack, owned.context.vector, ?_⟩
    rw [args.1, pointerNat]
    exact keptChild
  have qCode : CodeAt q base := by simpa only [CodeAt, q, block_program] using code
  have qError : read_err q = .None := (block_error _ current).trans error
  have qAligned : CheckSPAlignment q := block_aligned _ current aligned
  obtain ⟨fuel, final, executed, post⟩ :=
    induction source q base qOwned qCode qError qAligned qPC args.2
  refine ⟨4 + fuel, final, ?_, ?_⟩
  · rw [run_plus, qRun, executed]
  · refine ⟨post.returned, post.platform, ?_, post.result, qFrame.trans post.frame⟩
    exact post.program.trans (block_program vectorOps current)

end SszArm.Codec.Fixed.IsFixed
