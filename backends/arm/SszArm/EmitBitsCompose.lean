import SszArm.EmitBitsFinish
import SszArm.EmitBitsEncoding
import SszArm.EmitBitsTailGuards

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open Delimited (MemoryFrame)

@[simp] theorem prepared_vector (path : Path) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (prepared path s) = r (.SFP reg) s := by
  have readySame (state : ArmState) : r (.SFP reg) (ready path state) = r (.SFP reg) state := by
    cases path <;> simp [ready, block, Path.setupOps, Op.effect, Activation.put,
      Activation.next, state_simp_rules]
  have countedSame (state : ArmState) : r (.SFP reg) (counted path state) = r (.SFP reg) state := by
    simp [counted, countPair, Activation.put, Activation.next, state_simp_rules]
  have backingSame (state : ArmState) : r (.SFP reg) (backingLoaded state) = r (.SFP reg) state := by
    simp [backingLoaded, Activation.put, Activation.next, state_simp_rules]
  simp only [prepared, readySame, checked, guarded_vector, backingSame,
    quotientLoaded, shifted_vector, countedSame, routed_vector]

theorem produced_prepend {s u t : ArmState} {args : Args} {desc : Desc} {bits : Packed}
    {size : Nat} {base : BitVec 64} (post : Produced u t args desc (.bits bits) size base)
    (program : u.program = s.program) (frame : MemoryFrame (bodyWrites args size) s u)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 28#5, 29#5] → r (.GPR reg) u = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) u).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Produced s t args desc (.bits bits) size base := by
  exact ⟨post.pc, post.program.trans program, post.error, post.resultRegister, post.stack,
    post.length, post.bytes, frame.trans post.frame,
    fun reg member => (post.registers reg member).trans (registers reg member),
    fun reg low high => (post.vectors reg low high).trans (vectors reg low high)⟩

theorem prepend_copy (path : Path) {s t : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} {base : BitVec 64} (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (copyPost : CopyPost path.copySite (prepared path s) (copied path s bits) base)
    (post : Produced (copied path s bits) t args desc (.bits bits) size base) :
    Produced s t args desc (.bits bits) size base := by
  apply produced_prepend post (copyPost.program.trans (prepared_program path s))
    (copied_frame path kind owned registers copyPost)
  · intro reg member
    have copyUntouched : reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    have untouched : reg ∉ [0#5, 1#5, 2#5, 8#5, 9#5, 22#5, 23#5, 24#5, 25#5, 26#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    exact (copyPost.registers reg copyUntouched).trans (prepared_register path s reg untouched)
  · intro reg low high
    have nonzero : reg ≠ 0#5 := by bv_omega
    rw [copyPost.vectors reg nonzero, prepared_vector]

end SszArm.Emit.Bits
