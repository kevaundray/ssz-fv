import SszX86.CodecIsFixedResources

namespace SszX86.CodecIsFixed
open SszNative UintCodec BoolCodec

private theorem low_byte_replace (value : BitVec 64) (byte : BitVec 8) :
    (value.replaceLow byte).setWidth 8 = byte := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  simp only [BitVec.replaceLow, BitVec.setWidth_eq]
  exact BitVec.extractLsb'_append_eq_right (a := value.drop 8) (b := byte)

theorem true_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (bytes : Nat) :
    Eventually (step e) (BodyPost s bytes true base) (s, base + 51) := by
  apply true_runs e base hc
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩
  exact low_byte_replace _ _

theorem false_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (bytes : Nat) :
    Eventually (step e) (BodyPost s bytes false base) (s, base + 122) := by
  apply false_runs e base hc
  intro flags
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩

theorem working_entry {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {ra : BitVec 64} {bytes : Nat}
    (owned : Owned s base r desc ra bytes) :
    Working (savedState s) base r desc (bytes - 24) := by
  have enough : 24 ≤ bytes := (stackBytes_activation desc).trans owned.enough
  have frame := saved_frame s bytes enough
  have substack := owned.stack.substack 24 (bytes - 24) (by omega)
  refine ⟨owned.descriptor.frame frame owned.readonly,
    table_frame owned.table owned.table_readonly frame owned.readonly,
    owned.table_readonly, ?_, by omega, ?_, ?_⟩
  · refine ⟨substack.lowEnough, ?_⟩
    exact saved_mapped s _ _ substack.mapped
  · change (s.regs.rsp.toBitVec - 24).toNat + 32 ≤ 2 ^ 64
    have low := owned.stack.lowEnough
    have bound := owned.return_bound
    simp only [← UInt64.toNat_toBitVec] at low bound
    bv_omega
  · intro a input inside
    apply owned.readonly a input
    exact Codec.stack_subspan s.regs.rsp.toBitVec 24 (bytes - 24) bytes (by omega) a inside

/-- The original saved words stay above every body/recursive-call write. -/
theorem body_saved {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {ra : BitVec 64} {bytes : Nat} {t : MachineState}
    (owned : Owned s base r desc ra bytes)
    (post : BodyPost (savedState s) (bytes - 24) (FixedSize.isFixed desc) base t) :
    SavedAt t.1.dmem t.1.regs.rsp.toBitVec
      ⟨s.regs.rbx.toBitVec, s.regs.r14.toBitVec, ra⟩ := by
  have working := working_entry owned
  have preserved (offset : Nat) (bound : offset + 8 ≤ 32) :=
    frame_load_above (savedState s).regs.rsp.toBitVec (bytes - 24) offset 8
      working.stack.lowEnough (by
        have top := working.above
        simp only [UInt64.toNat_toBitVec]
        omega) post.frame
  rw [post.stack]
  unfold SavedAt
  rw [preserved 8 (by decide), preserved 16 (by decide), preserved 24 (by decide)]
  exact saved_at s ra owned.return_load

theorem body_frame {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {ra : BitVec 64} {bytes : Nat} {t : MachineState}
    (owned : Owned s base r desc ra bytes)
    (post : BodyPost (savedState s) (bytes - 24) (FixedSize.isFixed desc) base t) :
    Codec.MemoryFrame s.dmem t.1.dmem (Codec.StackWrites s.regs.rsp.toBitVec bytes) := by
  have enough : 24 ≤ bytes := (stackBytes_activation desc).trans owned.enough
  intro a outside
  have suboutside : ¬ Codec.StackWrites (savedState s).regs.rsp.toBitVec (bytes - 24) a := by
    intro inside
    apply outside
    exact Codec.stack_subspan s.regs.rsp.toBitVec 24 (bytes - 24) bytes (by omega) a inside
  exact (post.frame a suboutside).trans (saved_frame s bytes enough a outside)

/-- The exact epilogue restores the original ABI and outside-stack frame, with
no assumption that the Boolean classification is true. -/
theorem finish_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (ra : BitVec 64) (bytes : Nat) (owned : Owned s base r desc ra bytes)
    (t : MachineState)
    (post : BodyPost (savedState s) (bytes - 24) (FixedSize.isFixed desc) base t) :
    Eventually (step e) (Post s desc ra bytes) t := by
  let saved : Saved := ⟨s.regs.rbx.toBitVec, s.regs.r14.toBitVec, ra⟩
  have frame := body_frame owned post
  have finalPost : Post s desc ra bytes (returned t.1 saved, Int64.ofBitVec ra) := by
    refine ⟨?_, post.result, frame, ?_⟩
    · refine ⟨rfl, ?_, ?_, post.rbp, post.r12, post.r13, ?_, post.r15, post.vectors, ?_⟩
      · change t.1.regs.rsp.toBitVec + 32 = s.regs.rsp.toBitVec + 8
        rw [post.stack]
        change s.regs.rsp.toBitVec - 24 + 32 = s.regs.rsp.toBitVec + 8
        bv_omega
      · exact UInt64.ofBitVec_toBitVec _
      · exact UInt64.ofBitVec_toBitVec _
      · have preserved := frame_load_above s.regs.rsp.toBitVec bytes 0 8
          owned.stack.lowEnough (by simpa using owned.return_bound) frame
        simpa only [BitVec.ofNat_zero, BitVec.add_zero, owned.return_load] using preserved
    · intro p n hm
      exact post.mapped p n (saved_mapped s p n hm)
  have exits := epilogues e base hc t.1 saved (body_saved owned post) _ finalPost
  have pc := post.pc
  cases value : FixedSize.isFixed desc with
  | false =>
    have at : t.2 = base + 124 := by simpa only [value, Bool.false_eq_true, ↓reduceIte] using pc
    simpa only [← at] using exits.2
  | true =>
    have at : t.2 = base + 53 := by simpa only [value, ↓reduceIte] using pc
    simpa only [← at] using exits.1

end SszX86.CodecIsFixed
