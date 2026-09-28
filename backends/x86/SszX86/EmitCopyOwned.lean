import SszX86.EmitBodyOwned
import SszX86.EmitBytesMemory

namespace SszX86.Emit
open SszNative.Serialize UintCodec

theorem AtBody.bytes_owned {s t : MachineData} {base : Int64} {desc : Desc}
    {bytes : Ssz.Bytes} {buffer ra : BitVec 64} {written : Nat} (h : AtBody s t)
    (owned : Owned s base desc (.bytes bytes) buffer ra written)
    (tag : BodyTag desc (.bytes bytes) t) : Bytes.Owned t bytes buffer := by
  have compatible := success_compatible desc (.bytes bytes) written owned.valid.success
  have shape : descTag desc = 2 ∨ descTag desc = 3 := by
    cases desc <;> simp_all [Compatible, descTag]
  have encoding : emit desc (.bytes bytes) = bytes := by
    cases desc <;> simp_all [Compatible, emit]
  have length : written = bytes.size := by
    have counted := owned.valid.emitted_size
    rw [encoding] at counted
    exact counted.symm
  subst written
  refine {
    tag := ?_
    capacity := ?_
    length := ?_
    pointer := ?_
    source := ?_
    output := h.output_mapped owned
    result := h.result_mapped owned
    stack := ?_
    outputResult := h.output_result owned
    outputStack := ?_
    resultStack := ?_
    sourceOutput := ?_
    sourceStack := ?_ }
  · rcases shape with vector | list
    · left
      simpa only [vector] using tag.1
    · right
      simpa only [list] using tag.1
  · rw [h.capacity]
    exact owned.valid.fits
  · have unchanged := owned.value_load 16 8 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2.2.1
  · have unchanged := owned.value_load 8 8 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2.1
  · rw [h.memory]
    exact owned.saved_bytes buffer bytes
      (fun _ inside => Or.inr (Or.inr (Or.inr inside))) owned.valueStored.2.2.2.1
  · intro i hi
    exact h.stack_mapped owned i (by omega)
  · intro i hi j hj
    exact h.output_stack owned i hi j (by omega)
  · intro i hi j hj
    exact h.result_stack owned i hi j (by omega)
  · intro i hi j hj equal
    apply h.readonly owned _ (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))
    exact Or.inl ⟨j, hj, equal⟩
  · intro i hi j hj equal
    apply h.readonly owned _ (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))
    exact Or.inr (Or.inr ⟨j, by omega, equal⟩)

end SszX86.Emit
