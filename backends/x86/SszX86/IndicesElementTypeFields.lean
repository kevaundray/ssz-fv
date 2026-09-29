import SszX86.IndicesElementTypeReturns

namespace SszX86.IndicesElementType
open SszNative UintCodec

/-- Complete container body, including arbitrary ordinal normalization, native
usize bounds, Field24 selection, five physical copy loads, errors and RET. -/
theorem fields_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem) (progressive : Bool)
    (fields : List (String × SszNative.Codec.Desc)) (buffer : BitVec 64) (ordinal : NatOperand)
    (slice : Codec.SliceAt s.dmem readonly
      (t.regs.rsi.toBitVec + if progressive then 24 else 8) buffer fields.length 24 8)
    (stored : Codec.FieldsAt s.dmem readonly buffer fields)
    (index : Codec.NatAt s.dmem readonly (t.regs.rdx.toBitVec + 8) ordinal) :
    Eventually (step e) (Returned s readonly ra (SszNative.Indices.fieldType fields ordinal))
      (t, base + if progressive then 206 else 213) := by
  apply field_offset_cps e base hc t progressive
  let u : MachineData := {t with regs := {t.regs with rax := if progressive then 24 else 8}}
  have kept : Preserved s u := preserved
  have pointer : Mem.loadInt u.dmem (u.regs.rdx.toBitVec + 8) 8 =
      some (ordinal.pointer.toNat : Int) := by
    have load := widthLoad_eq s.dmem _ _ _ index.stored.1
    simpa [u, memory] using load
  have payload : Mem.loadInt u.dmem (u.regs.rdx.toBitVec + 16) 8 =
      some (ordinal.payload.toNat : Int) := by
    have load := widthLoad_eq s.dmem _ _ _ index.stored.2.1
    simpa [u, memory, width_address, BitVec.add_assoc] using load
  apply ordinal_cps e base hc u ordinal pointer payload
    (by simpa [u, memory] using index.stored.2.2)
  · intro fits previous flags
    let v := ordinalState u ordinal (SszNative.Indices.word ordinal 0) previous flags
    have keepV : Preserved s v := kept
    have sameV : v.dmem = s.dmem := memory
    have countLoad : Mem.loadInt v.dmem
        (v.regs.rsi.toBitVec + v.regs.rax.toBitVec + 8) 8 =
        some ((BitVec.ofNat 64 fields.length).toNat : Int) := by
      have count := slice.countBound
      cases progressive <;>
        simpa [v, u, ordinalState, memory, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt count] using slice.length.load
    have finish : ∀ flags', Eventually (step e)
        (Returned s readonly ra (SszNative.Indices.fieldType fields ordinal))
        ({v with status := flags'},
          if v.regs.rdx.toBitVec.toNat < (BitVec.ofNat 64 fields.length).toNat
          then base + 284 else base + 352) := by
      intro flags'
      have count : (BitVec.ofNat 64 fields.length).toNat = fields.length :=
        Nat.mod_eq_of_lt slice.countBound
      simp only [count]
      by_cases inside : (SszNative.Indices.word ordinal 0).toNat < fields.length
      · have result : SszNative.Indices.fieldType fields ordinal =
            .ok fields[(SszNative.Indices.word ordinal 0).toNat].2 := by
          simp [SszNative.Indices.fieldType, SszNative.Indices.ordinalToUsize, fits,
            List.getElem?_eq_getElem inside]
        simp only [v, ordinalState, UInt64.toBitVec_ofBitVec, inside, ↓reduceIte, result]
        obtain ⟨child, selected, childStored⟩ := fields_index stored
          (SszNative.Indices.word ordinal 0).toNat inside
        apply selected_pointer_cps e base hc _ buffer child
        · cases progressive <;> simpa [u, memory] using slice.pointer.load
        · simpa [memory, BitVec.ofNat_mul, BitVec.ofNat_toNat] using selected
        · apply copy_runs e base hc s _ readonly desc path ra _ owned
          · exact keepV
          · exact memory
          · exact childStored
      · have result : SszNative.Indices.fieldType fields ordinal =
            .error (.noSuchField ordinal) := by
          simp [SszNative.Indices.fieldType, SszNative.Indices.ordinalToUsize, fits,
            List.getElem?_eq_none (by omega : fields.length ≤
              (SszNative.Indices.word ordinal 0).toNat)]
        simp only [v, ordinalState, UInt64.toBitVec_ofBitVec, inside, ↓reduceIte, result]
        apply noSuchField_runs e base hc s _ readonly desc path ra ordinal owned
        · exact keepV
        · exact memory
        · rfl
        · rfl
    have branches := bounds_cps e base hc v (BitVec.ofNat 64 fields.length)
      countLoad _ finish
    cases empty : ordinal.words.isEmpty
    · simpa [empty, v] using branches.1
    · simpa [empty, v] using branches.2
  · intro wide indexWord previous flags
    have result : SszNative.Indices.fieldType fields ordinal =
        .error (.noSuchField ordinal) := by
      simp [SszNative.Indices.fieldType, SszNative.Indices.ordinalToUsize, show ¬ordinal.wordCount ≤ 1 by omega]
    rw [result]
    apply noSuchField_runs e base hc s _ readonly desc path ra ordinal owned
    · exact kept
    · exact memory
    · rfl
    · rfl

end SszX86.IndicesElementType
