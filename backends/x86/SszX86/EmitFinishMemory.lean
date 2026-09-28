import SszX86.EmitFinishResources

namespace SszX86.Emit
open SszNative.Serialize UintCodec BoolCodec

/-- The success record and encoding, with an exact pointwise write footprint. -/
structure SuccessMemory (s : MachineData) (desc : Desc) (value : Value)
    (written : Nat) (m : DataMem) : Prop where
  length : widthLoad m s.regs.rdi.toNat 8 = some written
  status : Mem.loadInt m (s.regs.rdi.toBitVec + 64) 4 = some 0
  output : BytesAt m s.regs.r8.toBitVec (emit desc value)
  frame : MemoryFrame s.dmem m (Writable s written)

variable {s body final : MachineData} {base : Int64} {desc : Desc} {value : Value}
  {buffer ra : BitVec 64} {written : Nat}

theorem AtBody.body_frame (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    MemoryFrame s.dmem final.dmem (Writable s written) := by
  intro a outside
  rw [post.frame a (by
    intro inside
    apply outside
    apply h.body_writable
    simpa only [owned.valid.emitted_size] using inside), h.memory]
  exact saved_frame s written a outside

theorem AtBody.output_status_apart (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    Large.Disjoint s.regs.r8.toBitVec (final.regs.rbx.toBitVec + 64) written 4 := by
  intro i hi j hj equal
  apply owned.outputResult i hi (64 + j) (by omega)
  rw [BitVec.ofNat_add]
  simpa only [post.result, h.result, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal

theorem AtBody.success_memory (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    SuccessMemory s desc value written (successState final).dmem := by
  have result : final.regs.rbx.toBitVec = s.regs.rdi.toBitVec :=
    congrArg UInt64.toBitVec (post.result.trans h.result)
  have live : BytesAt final.dmem s.regs.r8.toBitVec (emit desc value) := by
    simpa only [h.output] using post.output
  refine ⟨?_, ?_, ?_, ?_⟩
  · have measured := post.length
    rw [h.result, owned.valid.emitted_size] at measured
    have address : BitVec.ofNat 64 s.regs.rdi.toNat = s.regs.rdi.toBitVec := by
      change BitVec.ofNat 64 s.regs.rdi.toBitVec.toNat = s.regs.rdi.toBitVec
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    unfold widthLoad at measured ⊢
    simp only [successState, result, address] at measured ⊢
    rw [load_store_disjoint final.dmem s.regs.rdi.toBitVec
      (s.regs.rdi.toBitVec + 64) 8 4 0 (by intro i hi j hj; bv_omega)]
    exact measured
  · rw [successState, result, load_store_same final.dmem _ 4 0 (by decide)]
    exact congrArg some (show Int.take 32 0 = 0 by decide)
  · intro i hi
    apply Eq.trans (memmove_store_lookup_outside final.dmem _ _ _ (by
      intro j hj
      exact h.output_status_apart owned post i
        (by simpa only [owned.valid.emitted_size] using hi) j
        (by simpa only [Int.toBytes_length] using hj)))
    exact live i hi
  · intro a outside
    apply Eq.trans (memmove_store_lookup_outside final.dmem _ _ _ (by
      intro i hi equal
      apply outside
      right; right; left
      refine ⟨i, by simpa only [Int.toBytes_length] using hi, ?_⟩
      simpa only [result] using equal))
    exact h.body_frame owned post a outside

theorem Owned.tail_protected (owned : Owned s base desc value buffer ra written)
    (i : Nat) (afterPrefix : written ≤ i) (inside : i < s.regs.r9.toNat) :
    ¬ Writable s written (s.regs.r8.toBitVec + BitVec.ofNat 64 i) := by
  intro writes
  rcases writes with live | other
  · obtain ⟨j, hj, equal⟩ := live
    have index := memmove_addr_injective s.regs.r8.toBitVec s.regs.r9.toNat i j
      owned.outputBound inside (by have fits := owned.valid.fits; omega) equal
    omega
  · exact owned.tailReadonly i afterPrefix inside other

theorem SuccessMemory.output_frame {m : DataMem}
    (post : SuccessMemory s desc value written m)
    (owned : Owned s base desc value buffer ra written) :
    ∀ i < s.regs.r9.toNat,
      m.get? (s.regs.r8.toBitVec + BitVec.ofNat 64 i) =
        applyWrites (fun j => s.dmem.get? (s.regs.r8.toBitVec + BitVec.ofNat 64 j))
          (emit desc value) i := by
  intro i hi
  by_cases live : i < (emit desc value).size
  · rw [applyWrites_prefix _ _ _ live, Array.getElem?_eq_getElem live]
    exact post.output i live
  · rw [applyWrites_tail _ _ _ (by omega)]
    apply post.frame
    apply owned.tail_protected i
    · simpa only [owned.valid.emitted_size] using Nat.le_of_not_gt live
    · exact hi

theorem SuccessMemory.borrowed_frame {m : DataMem}
    (post : SuccessMemory s desc value written m)
    (owned : Owned s base desc value buffer ra written) :
    ∀ a, Borrowed s desc value buffer a → m.get? a = s.dmem.get? a := by
  intro a borrowed
  exact post.frame a (owned.readonly a borrowed)

end SszX86.Emit
