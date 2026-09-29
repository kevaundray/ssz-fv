import SszX86.IndicesElementTypeOwned

namespace SszX86.IndicesElementType
open SszNative UintCodec

/-- Register-only invariant of all blocks in this leaf function. -/
structure Preserved (s t : MachineData) : Prop where
  output : t.regs.rdi = s.regs.rdi
  stack : t.regs.rsp = s.regs.rsp
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  simd : t.zmms = s.zmms

theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (result : Except SszNative.Indices.Error SszNative.Codec.Desc)
    (active : ResultMemory s.dmem readonly s.regs.rdi.toBitVec result t.dmem)
    (bytes : Nat) (bound : bytes ≤ 64)
    (frame : Codec.MemoryFrame s.dmem t.dmem (SuccessWrites s.regs.rdi.toBitVec bytes)) :
    Eventually (step e) (Returned s readonly ra result) (t, base + 75) ∧
    Eventually (step e) (Returned s readonly ra result) (t, base + 120) ∧
    Eventually (step e) (Returned s readonly ra result) (t, base + 205) ∧
    Eventually (step e) (Returned s readonly ra result) (t, base + 342) ∧
    Eventually (step e) (Returned s readonly ra result) (t, base + 414) := by
  apply ret_cps e base hc t ra (Returned s readonly ra result)
  · rw [preserved.stack]
    exact owned.return_after t.dmem bytes bound frame
  · exact ⟨rfl, by simp [preserved.stack], preserved.rbx, preserved.rbp,
      preserved.r12, preserved.r13, preserved.r14, preserved.r15, preserved.simd, active⟩

theorem bool_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem) :
    Eventually (step e) (Returned s readonly ra (.ok (.primitive .bool))) (t, base + 61) := by
  apply bool_cps e base hc t
  · simpa [OutputMapped, memory, preserved.output] using owned.output
  · apply (finish_cps e base hc s _ readonly desc path ra owned preserved
      (.ok (.primitive .bool)) _ 8 (by decide) _).1
    · simpa [memory, preserved.output] using ResultMemory.bool (original := s.dmem)
        (readonly := readonly) (out := s.regs.rdi.toBitVec)
    · simpa [memory, preserved.output] using bool_frame s.dmem s.regs.rdi.toBitVec

theorem uint_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem) :
    Eventually (step e) (Returned s readonly ra (.ok (.primitive (.uint (.small 1)))))
      (t, base + 90) := by
  apply uint_cps e base hc t
  · simpa [OutputMapped, memory, preserved.output] using owned.output
  · apply (finish_cps e base hc s _ readonly desc path ra owned preserved
      (.ok (.primitive (.uint (.small 1)))) _ 24 (by decide) _).2.1
    · simpa [memory, preserved.output] using ResultMemory.uint (original := s.dmem)
        (readonly := readonly) (out := s.regs.rdi.toBitVec)
    · simpa [memory, preserved.output] using uint_frame s.dmem s.regs.rdi.toBitVec

theorem notSteppable_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem) :
    Eventually (step e) (Returned s readonly ra (.error .notSteppable)) (t, base + 135) := by
  apply notSteppable_cps e base hc t
  · simpa [OutputMapped, memory, preserved.output] using owned.output
  · apply (finish_cps e base hc s _ readonly desc path ra owned preserved
      (.error .notSteppable) _ 64 (by decide) _).2.2.1
    · simpa [memory, preserved.output] using ResultMemory.notSteppable (original := s.dmem)
        (readonly := readonly) (out := s.regs.rdi.toBitVec)
    · simpa [memory, preserved.output] using error_frame s.dmem s.regs.rdi.toBitVec 0 0 56

theorem noSuchField_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64) (ordinal : NatOperand)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem) (pointer : t.regs.r8.toBitVec = ordinal.pointer)
    (payload : t.regs.rcx.toBitVec = ordinal.payload) :
    Eventually (step e) (Returned s readonly ra (.error (.noSuchField ordinal)))
      (t, base + 352) := by
  apply noSuchField_cps e base hc t
  · simpa [OutputMapped, memory, preserved.output] using owned.output
  · apply (finish_cps e base hc s _ readonly desc path ra owned preserved
      (.error (.noSuchField ordinal)) _ 64 (by decide) _).2.2.2.2
    · simpa [memory, preserved.output, pointer, payload] using
        ResultMemory.noSuchField (original := s.dmem) (readonly := readonly)
          (out := s.regs.rdi.toBitVec) ordinal
    · simpa [memory, preserved.output, pointer, payload] using
        error_frame s.dmem s.regs.rdi.toBitVec ordinal.pointer ordinal.payload 57

theorem copy_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64) (child : SszNative.Codec.Desc)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem)
    (stored : Codec.DescAt s.dmem readonly t.regs.rax.toBitVec child) :
    Eventually (step e) (Returned s readonly ra (.ok child)) (t, base + 297) := by
  obtain ⟨words, input⟩ := owned.child_words stored
  apply copy_cps e base hc t words
  · simpa [memory] using input
  · simpa [OutputMapped, memory, preserved.output] using owned.output
  · simpa [preserved.output] using owned.child_apart stored
  · have keep : Preserved s (copied t words) := preserved
    apply (finish_cps e base hc s _ readonly desc path ra owned keep
      (.ok child) _ 40 (by decide) _).2.2.2.1
    · simpa [copied, memory, preserved.output] using ResultMemory.copied words stored input
    · simpa [copied, memory, preserved.output] using copy_frame s.dmem s.regs.rdi.toBitVec words

end SszX86.IndicesElementType
