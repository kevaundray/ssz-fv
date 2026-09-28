import SszX86.EmitBodyOwned
import SszX86.EmitBool
import SszX86.EmitBitsMemory

namespace SszX86.Emit
open SszNative SszNative.Serialize UintCodec

theorem AtBody.bool_owned {s t : MachineData} {base : Int64} {value : Bool}
    {buffer ra : BitVec 64} {written : Nat} (h : AtBody s t)
    (owned : Owned s base .bool (.bool value) buffer ra written)
    (tag : BodyTag .bool (.bool value) t) : BoolOwned t value := by
  have length : 1 = written := Except.ok.inj owned.valid.success
  subst written
  refine ⟨tag.2 (by decide), ?_, ?_, h.output_mapped owned,
    h.result_mapped owned, h.output_result owned⟩
  · rw [h.capacity]
    exact owned.valid.fits
  · have unchanged := owned.value_load 1 1 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [ValuePayloadAt, BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2

theorem AtBody.bits_owned {s t : MachineData} {base : Int64} {desc : Desc} {bits : Packed}
    {buffer ra : BitVec 64} {written : Nat} (h : AtBody s t)
    (owned : Owned s base desc (.bits bits) buffer ra written)
    (tag : BodyTag desc (.bits bits) t) : Bits.Owned t desc bits buffer written := by
  have kind : Bits.IsBits desc := by
    have compatible := success_compatible desc (.bits bits) written owned.valid.success
    cases desc <;> simp_all [Compatible, Bits.IsBits]
  refine {
    kind := kind
    valid := h.valid owned
    tag := tag.1
    physical := owned.physical
    pointer := ?_
    length := ?_
    low := ?_
    high := ?_
    source := ?_
    outputMapped := h.output_mapped owned
    resultMapped := h.result_mapped owned
    stackMapped := h.stack_mapped owned
    outputResult := h.output_result owned
    outputStack := h.output_stack owned
    resultStack := h.result_stack owned
    headerProtected := ?_
    sourceProtected := ?_ }
  · have unchanged := owned.value_load 16 8 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2.1
  · have unchanged := owned.value_load 24 8 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2.2.1
  · have unchanged := owned.value_load 32 8 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2.2.2.1
  · have unchanged := owned.value_load 40 8 (by dsimp only [valueBytes]; decide)
    rw [h.memory, h.valuePointer]
    simpa only [BitVec.ofNat_eq_ofNat, unchanged] using owned.valueStored.2.2.2.2.1
  · rw [h.memory]
    apply owned.saved_bytes buffer bits.bytes
    · intro a inside
      exact Or.inr (Or.inr (Or.inr inside))
    · exact owned.valueStored.2.2.2.2.2.1
  · intro a inside
    apply h.readonly owned a
    right; left
    simpa only [h.valuePointer, valueBytes] using inside
  · intro a inside
    exact h.readonly owned a (Or.inr (Or.inr (Or.inr inside)))

end SszX86.Emit
