import SszCodecEmitPlans

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value)
open CodecMeasure (Plan Parts)

/-- Semantic child encodings, paired in declaration order. This is proof data,
not an alternative implementation of the native emitter. -/
inductive ByteChildren : Parts → List Value → List (Bool × Ssz.Bytes) → Prop where
  | repeatedNil (desc : Desc) : ByteChildren (.repeated desc) [] []
  | fieldsNil : ByteChildren (.fields []) [] []
  | repeated (desc : Desc) (value : Value) (values : List Value)
      (bytes : Ssz.Bytes) (slots : List (Bool × Ssz.Bytes))
      (encoded : Ssz.serialize desc.erase value.erase = .ok bytes)
      (remaining : ByteChildren (.repeated desc) values slots) :
      ByteChildren (.repeated desc) (value :: values) ((FixedSize.isFixed desc, bytes) :: slots)
  | fields (name : String) (desc : Desc) (fields : List (String × Desc))
      (value : Value) (values : List Value) (bytes : Ssz.Bytes)
      (slots : List (Bool × Ssz.Bytes))
      (encoded : Ssz.serialize desc.erase value.erase = .ok bytes)
      (remaining : ByteChildren (.fields fields) values slots) :
      ByteChildren (.fields ((name, desc) :: fields)) (value :: values)
        ((FixedSize.isFixed desc, bytes) :: slots)

private theorem except_bind_ok {α β : Type} (first : Except Ssz.Err α)
    (next : α → Except Ssz.Err β) (result : β) :
    first.bind next = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Except.bind]

private theorem constant_zip (fixed : Bool) (parts : List Ssz.Bytes) :
    (parts.map (fun _ => fixed)).zip parts = parts.map (fun bytes => (fixed, bytes)) := by
  induction parts with
  | nil => rfl
  | cons bytes rest ih => simp only [List.map_cons, List.zip_cons_cons, ih]

private theorem each_byteChildren (desc : Desc) (values : List Value)
    (parts : List Ssz.Bytes)
    (encoded : Ssz.serializeEach desc.erase (Value.eraseList values) = .ok parts) :
    ByteChildren (.repeated desc) values
      (parts.map (fun bytes => (FixedSize.isFixed desc, bytes))) := by
  induction values generalizing parts with
  | nil =>
    simp only [Value.eraseList, Ssz.serializeEach, Except.ok.injEq] at encoded
    subst parts
    exact .repeatedNil desc
  | cons value values ih =>
    simp only [Value.eraseList, Ssz.serializeEach, Bind.bind] at encoded
    obtain ⟨bytes, first, encoded⟩ := (except_bind_ok _ _ _).1 encoded
    obtain ⟨rest, remaining, encoded⟩ := (except_bind_ok _ _ _).1 encoded
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at encoded
    subst parts
    exact .repeated desc value values bytes _ first (ih rest remaining)

private theorem fields_byteChildren (fields : List (String × Desc)) (values : List Value)
    (parts : List Ssz.Bytes)
    (encoded : Ssz.serializeFields (Desc.eraseFields fields) (Value.eraseList values) = .ok parts) :
    ByteChildren (.fields fields) values
      (((Desc.eraseFields fields).map Ssz.Desc.isFixed).zip parts) := by
  induction values generalizing fields parts with
  | nil =>
    cases fields with
    | nil =>
      simp only [Value.eraseList, Desc.eraseFields, Ssz.serializeFields,
        Except.ok.injEq] at encoded
      subst parts
      exact .fieldsNil
    | cons field fields =>
      simp only [Value.eraseList, Desc.eraseFields, Ssz.serializeFields] at encoded
      cases encoded
  | cons value values ih =>
    cases fields with
    | nil =>
      simp only [Value.eraseList, Desc.eraseFields, Ssz.serializeFields] at encoded
      cases encoded
    | cons field fields =>
      rcases field with ⟨name, desc⟩
      simp only [Value.eraseList, Desc.eraseFields, Ssz.serializeFields, Bind.bind] at encoded
      obtain ⟨bytes, first, encoded⟩ := (except_bind_ok _ _ _).1 encoded
      obtain ⟨rest, remaining, encoded⟩ := (except_bind_ok _ _ _).1 encoded
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at encoded
      subst parts
      simpa only [Desc.eraseFields, List.map_cons, List.zip_cons_cons,
        FixedSize.isFixed_isFixed] using
        ByteChildren.fields name desc fields value values bytes _ first (ih fields rest remaining)

private theorem assemble_bytes (flags : List Bool) (parts : List Ssz.Bytes)
    (bytes : Ssz.Bytes) (encoded : Ssz.assemble flags parts = .ok bytes) :
    bytes = Ssz.headOf (Ssz.headWidth (flags.zip parts)) (flags.zip parts) ++
      Ssz.bodiesOf (flags.zip parts) := by
  unfold Ssz.assemble at encoded
  dsimp only at encoded
  split at encoded
  · cases encoded
  · change (Except.ok (Ssz.headOf (Ssz.headWidth (flags.zip parts)) (flags.zip parts) ++
        Ssz.bodiesOf (flags.zip parts)) : Except Ssz.Err Ssz.Bytes) = .ok bytes at encoded
    exact (Except.ok.inj encoded).symm

private theorem sequence_byteChildren (desc : Desc) (values : List Value)
    (bytes : Ssz.Bytes)
    (encoded : Ssz.serializeSequence desc.erase (Value.eraseList values) = .ok bytes) :
    ∃ slots, ByteChildren (.repeated desc) values slots ∧
      bytes = Ssz.headOf (Ssz.headWidth slots) slots ++ Ssz.bodiesOf slots := by
  simp only [Ssz.serializeSequence, Bind.bind] at encoded
  obtain ⟨parts, first, encoded⟩ := (except_bind_ok _ _ _).1 encoded
  refine ⟨parts.map (fun bytes => (FixedSize.isFixed desc, bytes)),
    each_byteChildren desc values parts first, ?_⟩
  simpa only [constant_zip, FixedSize.isFixed_isFixed] using assemble_bytes _ _ bytes encoded

private theorem struct_byteChildren (fields : List (String × Desc)) (values : List Value)
    (bytes : Ssz.Bytes)
    (encoded : Ssz.serializeStruct (Desc.eraseFields fields) (Value.eraseList values) = .ok bytes) :
    ∃ slots, ByteChildren (.fields fields) values slots ∧
      bytes = Ssz.headOf (Ssz.headWidth slots) slots ++ Ssz.bodiesOf slots := by
  simp only [Ssz.serializeStruct, Bind.bind] at encoded
  obtain ⟨parts, first, encoded⟩ := (except_bind_ok _ _ _).1 encoded
  exact ⟨_, fields_byteChildren fields values parts first, assemble_bytes _ _ bytes encoded⟩

/-- A successful composite serialization exposes every child, including empty
payloads and heterogeneous fixed/variable fields. -/
theorem composite_byteChildren (desc : Desc) (parts : Parts) (values : List Value)
    (shape : Composite desc parts) (bytes : Ssz.Bytes)
    (semantic : Ssz.serialize desc.erase (Value.seq values).erase = .ok bytes) :
    ∃ slots, ByteChildren parts values slots ∧
      bytes = Ssz.headOf (Ssz.headWidth slots) slots ++ Ssz.bodiesOf slots := by
  cases shape with
  | vector element length =>
    simp only [Desc.erase_vector, Value.erase, Ssz.serialize] at semantic
    split at semantic
    · exact sequence_byteChildren element values bytes semantic
    · cases semantic
  | list element limit =>
    simp only [Desc.erase_list, Value.erase, Ssz.serialize] at semantic
    split at semantic
    · exact sequence_byteChildren element values bytes semantic
    · cases semantic
  | progressiveList element limit =>
    simp only [Desc.erase_progressiveList, Value.erase, Ssz.serialize, Bind.bind] at semantic
    obtain ⟨_, _, semantic⟩ := (except_bind_ok _ _ _).1 semantic
    exact sequence_byteChildren element values bytes semantic
  | container fields =>
    simp only [Desc.erase_container, Value.erase, Ssz.serialize] at semantic
    exact struct_byteChildren fields values bytes semantic
  | progressiveContainer active fields =>
    simp only [Desc.erase_progressiveContainer, Value.erase, Ssz.serialize] at semantic
    exact struct_byteChildren fields values bytes semantic
end SszNative.CodecEmit
