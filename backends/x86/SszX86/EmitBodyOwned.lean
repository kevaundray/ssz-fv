import SszX86.EmitEntry

namespace SszX86.Emit
open SszNative SszNative.Serialize UintCodec

variable {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
  {buffer ra : BitVec 64} {written : Nat}

theorem AtBody.local_base (h : AtBody s t) :
    t.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - 160 := by
  rw [h.stack]
  bv_omega

theorem AtBody.body_writable (h : AtBody s t) {a : BitVec 64}
    (inside : BodyWritable t written a) : Writable s written a := by
  rcases inside with output | result | scratch
  · left
    simpa only [h.output] using output
  · right; left
    simpa only [h.result] using result
  · obtain ⟨i, hi, equal⟩ := scratch
    right; right; right
    refine ⟨i, by omega, ?_⟩
    simpa only [h.local_base] using equal

theorem AtBody.readonly (h : AtBody s t) (owned : Owned s base desc value buffer ra written)
    (a : BitVec 64) (borrowed : Borrowed s desc value buffer a) : ¬ BodyWritable t written a :=
  fun inside => owned.readonly a borrowed (h.body_writable inside)

theorem AtBody.valid (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    ValidCall desc value t.regs.r9.toNat written := by
  rw [h.capacity]
  exact owned.valid

theorem AtBody.output_mapped (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    Large.Mapped t.dmem t.regs.r14.toBitVec written := by
  rw [h.memory, h.output]
  exact Dispatch.saved_mapped s _ _ owned.outputMapped

theorem AtBody.result_mapped (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    Large.Mapped t.dmem t.regs.rbx.toBitVec 8 := by
  rw [h.memory, h.result]
  exact Dispatch.saved_mapped s _ _ owned.lengthMapped

theorem AtBody.stack_mapped (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    Large.Mapped t.dmem (t.regs.rsp.toBitVec - 8) 112 := by
  rw [h.memory, h.local_base]
  have mappedBytes := Dispatch.saved_mapped s _ _ owned.stackMapped
  intro i hi
  exact mappedBytes i (by omega)

theorem AtBody.output_result (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    Large.Disjoint t.regs.r14.toBitVec t.regs.rbx.toBitVec written 8 := by
  rw [h.output, h.result]
  intro i hi j hj
  exact owned.outputResult i hi j (by omega)

theorem AtBody.output_stack (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    Large.Disjoint t.regs.r14.toBitVec (t.regs.rsp.toBitVec - 8) written 112 := by
  rw [h.output, h.local_base]
  intro i hi j hj
  exact owned.outputStack i hi j (by omega)

theorem AtBody.result_stack (h : AtBody s t) (owned : Owned s base desc value buffer ra written) :
    Large.Disjoint t.regs.rbx.toBitVec (t.regs.rsp.toBitVec - 8) 8 112 := by
  rw [h.result, h.local_base]
  intro i hi j hj
  exact owned.resultStack i (by omega) j (by omega)

theorem Owned.descriptor_load (owned : Owned s base desc value buffer ra written)
    (byteOffset byteCount : Nat) (within : byteOffset + byteCount ≤ descBytes desc) :
    Mem.loadInt (savedMem s) (s.regs.rsi.toBitVec + BitVec.ofNat 64 byteOffset) byteCount =
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 byteOffset) byteCount := by
  apply owned.saved_load
  intro a inside
  exact Or.inl (span_shift _ _ _ _ within inside)

theorem Owned.value_load (owned : Owned s base desc value buffer ra written)
    (byteOffset byteCount : Nat) (within : byteOffset + byteCount ≤ valueBytes value) :
    Mem.loadInt (savedMem s) (s.regs.rdx.toBitVec + BitVec.ofNat 64 byteOffset) byteCount =
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 byteOffset) byteCount := by
  apply owned.saved_load
  intro a inside
  exact Or.inr (Or.inl (span_shift _ _ _ _ within inside))

theorem Owned.saved_nat (owned : Owned s base desc value buffer ra written)
    (p : BitVec 64) (operand : NatOperand)
    (header : ∀ a, InSpan a p 16 → Borrowed s desc value buffer a)
    (limbs : ∀ a, NatBorrowed operand a → Borrowed s desc value buffer a)
    (stored : NatAt s.dmem p operand) : NatAt (savedMem s) p operand :=
  natAt_frame _ _ _ (saved_frame s written) p operand
    (fun a inside => owned.readonly a (header a inside))
    (fun a inside => owned.readonly a (limbs a inside)) stored

end SszX86.Emit
