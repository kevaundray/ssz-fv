import SszX86.CodecEmitLeafReturnResources

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec BoolCodec

structure LeafSuccessMemory (s : MachineData) (shape : Serialize.Desc)
    (value : SszNative.Codec.Value) (written : Nat) (m : DataMem) : Prop where
  length : widthLoad m s.regs.rdi.toNat 8 = some written
  status : Mem.loadInt m (s.regs.rdi.toBitVec + 64) 4 = some 0
  output : Emit.BytesAt m s.regs.r8.toBitVec (Serialize.emit shape value.toPrimitive)
  frame : SszX86.Codec.MemoryFrame s.dmem m (Writable s (.primitive shape) written)

variable {s body final : MachineData} {base : Int64} {shape : Serialize.Desc}
  {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
  {r : SszX86.Codec.Footprint} {ra : BitVec 64}

theorem leaf_body_frame (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    SszX86.Codec.MemoryFrame s.dmem final.dmem
      (Writable s (.primitive shape) owned.call.measured.size.value) := by
  intro a outside
  rw [post.frame a (by
    intro inside
    apply outside
    apply body_writable_sub anchors a
    simpa only [owned.call.primitive_valid.emitted_size] using inside), anchors.memory]
  apply SszX86.Codec.savedSix_frame s (stackBytes (.primitive shape))
    (by have := stackBytes_min (.primitive shape); omega) a
  exact fun inside => outside (Or.inr (Or.inr (Or.inr inside)))

theorem leaf_success_memory (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    LeafSuccessMemory s shape value owned.call.measured.size.value (Emit.successState final).dmem := by
  have result : final.regs.rbx.toBitVec = s.regs.rdi.toBitVec :=
    congrArg UInt64.toBitVec (post.result.trans anchors.result)
  have live : Emit.BytesAt final.dmem s.regs.r8.toBitVec (Serialize.emit shape value.toPrimitive) := by
    simpa only [anchors.output] using post.output
  have outputStatus : Large.Disjoint s.regs.r8.toBitVec
      (final.regs.rbx.toBitVec + 64) owned.call.measured.size.value 4 := by
    intro i hi j hj equal
    apply owned.outputResult i (Nat.lt_of_lt_of_le hi owned.call.fits) (64 + j) (by omega)
    rw [BitVec.ofNat_add]
    simpa only [result, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal
  refine ⟨?_, ?_, ?_, ?_⟩
  · have measured := post.length
    rw [anchors.result, owned.call.primitive_valid.emitted_size] at measured
    have address : BitVec.ofNat 64 s.regs.rdi.toNat = s.regs.rdi.toBitVec := by
      change BitVec.ofNat 64 s.regs.rdi.toBitVec.toNat = s.regs.rdi.toBitVec
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    unfold widthLoad at measured ⊢
    simp only [Emit.successState, result, address] at measured ⊢
    rw [load_store_disjoint final.dmem s.regs.rdi.toBitVec
      (s.regs.rdi.toBitVec + 64) 8 4 0 (by intro i hi j hj; bv_omega)]
    exact measured
  · rw [Emit.successState, result, load_store_same final.dmem _ 4 0 (by decide)]
    exact congrArg some (show Int.take 32 0 = 0 by decide)
  · intro i hi
    apply Eq.trans (memmove_store_lookup_outside final.dmem _ _ _ (by
      intro j hj
      exact outputStatus i (by simpa only [owned.call.primitive_valid.emitted_size] using hi)
        j (by simpa only [Int.toBytes_length] using hj)))
    exact live i hi
  · intro a outside
    apply Eq.trans (memmove_store_lookup_outside final.dmem _ _ _ (by
      intro i hi equal
      apply outside
      right; right; left
      exact ⟨i, by simpa only [Int.toBytes_length] using hi, by simpa only [result] using equal⟩))
    exact leaf_body_frame anchors owned post a outside

/-- Any exact output suffix is disjoint from every actually writable region.
This is derived from the caller's physical slice bounds and separation, not
from an assertion that those bytes happened to remain unchanged. -/
theorem Owned.tail_protected {desc : SszNative.Codec.Desc}
    (owned : Owned s base desc value supplied r ra)
    (i : Nat) (afterPrefix : owned.call.measured.size.value ≤ i) (inside : i < s.regs.r9.toNat) :
    ¬ Writable s desc owned.call.measured.size.value (s.regs.r8.toBitVec + BitVec.ofNat 64 i) := by
  intro writes
  rcases writes with output | result | status | stack
  · obtain ⟨j, hj, equal⟩ := output
    have index := memmove_addr_injective s.regs.r8.toBitVec s.regs.r9.toNat i j
      owned.outputBound inside (Nat.lt_of_lt_of_le hj owned.call.fits) equal
    omega
  · obtain ⟨j, hj, equal⟩ := result
    exact owned.outputResult i inside j (by omega) equal
  · obtain ⟨j, hj, equal⟩ := status
    apply owned.outputResult i inside (64 + j) (by omega)
    rw [BitVec.ofNat_add]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal
  · obtain ⟨j, hj, equal⟩ := stack
    exact owned.outputStack i inside j (by omega) equal

theorem leaf_output_trace {m : DataMem}
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (memory : LeafSuccessMemory s shape value owned.call.measured.size.value m) :
    OutputAt s.dmem m s.regs.r8.toBitVec s.regs.r9.toNat
      (SszNative.CodecEmit.emit (.primitive shape) value supplied
        ⟨s.regs.r8.toNat, s.regs.r9.toNat⟩).writes := by
  have valid := owned.call.primitive_valid
  have semantic : Ssz.serialize (SszNative.Codec.Desc.primitive shape).erase value.erase =
      .ok (Serialize.emit shape value.toPrimitive) := by
    simpa only [SszNative.Codec.Desc.erase, SszNative.Codec.Value.erase_toPrimitive] using valid.pinned
  have encoded := owned.call.encodes s.regs.r8.toNat (Serialize.emit shape value.toPrimitive) semantic
  apply OutputAt.of_bytes (by simpa only [UInt64.toNat_toBitVec] using encoded) memory.output
  intro i lower upper
  exact memory.frame _ (owned.tail_protected i (by simpa only [valid.emitted_size] using lower) upper)

end SszX86.CodecEmit
