import SszX86.CodecIsFixedLoop
import SszX86.CodecStorageViews

namespace SszX86.CodecIsFixed
open SszNative UintCodec BoolCodec

/-- The unsigned guard is proved from the loaded physical tag before the
actual table sequence; no desired branch outcome is an entry premise. -/
theorem bounded_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Nat) (bound : tag < 12)
    (index : s.regs.rax = UInt64.ofNat tag) (table : TableAt s.dmem base)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (jumped {s with status := flags} base tag, base + Int64.ofNat (tableEntry tag))) :
    Eventually (step e) P (s, base + 29) := by
  have bounded : s.regs.rax.toNat ≤ 11 := by
    rw [index]
    change (BitVec.ofNat 64 tag).toNat ≤ 11
    bv_omega
  apply range_guard e base hc
  · intro _ flags
    exact jump_runs e base hc {s with status := flags} tag P bound index table (next flags)
  · intro above
    omega

theorem fields_at73 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r : Codec.Footprint) (bytes : Nat)
    (fields : List (String × SszNative.Codec.Desc)) (pointer : BitVec 64)
    (children : ∀ field ∈ fields, EntryRefines e base field.2)
    (slice : Codec.SliceAt s.dmem r (s.regs.rdi.toBitVec + s.regs.rax.toBitVec)
      pointer fields.length 24 8)
    (stored : Codec.FieldsAt s.dmem r pointer fields)
    (table : TableAt s.dmem base)
    (table_readonly : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i))
    (stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec bytes)
    (enough : fieldsStackBytes fields ≤ bytes)
    (above : s.regs.rsp.toNat + 32 ≤ 2 ^ 64)
    (readonly : ∀ a, r a → ¬ Codec.StackWrites s.regs.rsp.toBitVec bytes a) :
    Eventually (step e) (BodyPost s bytes (FixedSize.fieldsFixed fields) base) (s, base + 73) := by
  apply fields_setup e base hc s pointer fields.length _ slice.pointer.load slice.length.load
  intro flags
  let prepared := fieldsState s pointer fields.length flags
  have owns : FieldsOwned prepared base r fields bytes :=
    ⟨stored, rfl, by have bound := slice.byteBound; omega, table, table_readonly,
      stack, enough, above, readonly⟩
  apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.fieldsFixed fields) base) _ _
  · exact fields_runs e base hc fields children prepared r bytes owns
  · intro t post
    apply Eventually.done
    exact post.preceded ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩

theorem container_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r : Codec.Footprint) (bytes : Nat)
    (fields : List (String × SszNative.Codec.Desc))
    (children : ∀ field ∈ fields, EntryRefines e base field.2)
    (owned : Working s base r (.container fields) bytes) :
    Eventually (step e) (BodyPost s bytes (FixedSize.fieldsFixed fields) base) (s, base + 68) := by
  obtain ⟨pointer, slice, stored⟩ := Codec.DescAt.container owned.descriptor
  apply container_offset e base hc
  let prepared : MachineData := {s with regs := {s.regs with rax := 8}}
  apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.fieldsFixed fields) base) _ _
  · apply fields_at73 e base hc prepared r bytes fields pointer children slice stored
      owned.table owned.table_readonly owned.stack
    · have enough := owned.enough
      simp only [stackBytes] at enough
      omega
    · exact owned.above
    · exact owned.readonly
  · intro t post
    apply Eventually.done
    exact post.preceded ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩

theorem progressive_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r : Codec.Footprint) (bytes : Nat) (active : List Bool)
    (fields : List (String × SszNative.Codec.Desc))
    (children : ∀ field ∈ fields, EntryRefines e base field.2)
    (owned : Working s base r (.progressiveContainer active fields) bytes) :
    Eventually (step e) (BodyPost s bytes (FixedSize.fieldsFixed fields) base) (s, base + 61) := by
  obtain ⟨pointer, slice, stored⟩ := Codec.DescAt.progressiveContainer owned.descriptor
  apply progressive_offset e base hc
  let prepared : MachineData := {s with regs := {s.regs with rax := 24}}
  apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.fieldsFixed fields) base) _ _
  · apply fields_at73 e base hc prepared r bytes fields pointer children slice stored
      owned.table owned.table_readonly owned.stack
    · have enough := owned.enough
      simp only [stackBytes] at enough
      omega
    · exact owned.above
    · exact owned.readonly
  · intro t post
    apply Eventually.done
    exact post.preceded ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩

/-- Every non-vector tag is routed through its actual guarded table slot, except
compatibleUnion tag12 which takes the native unsigned-above edge. -/
theorem nonvector_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (desc : SszNative.Codec.Desc)
    (notVector : ∀ element length, desc ≠ .vector element length)
    (children : ∀ fields, (desc = .container fields ∨ ∃ active, desc = .progressiveContainer active fields) →
      ∀ field ∈ fields, EntryRefines e base field.2)
    (s : MachineData) (r : Codec.Footprint) (bytes : Nat)
    (owned : Working s base r desc bytes)
    (tag : s.regs.rax = UInt64.ofNat (Codec.descTag desc)) :
    Eventually (step e) (BodyPost s bytes (FixedSize.isFixed desc) base) (s, base + 29) := by
  cases desc with
  | vector element length => exact False.elim (notVector element length rfl)
  | compatibleUnion variants =>
    have high : 11 < s.regs.rax.toNat := by rw [tag]; decide
    apply range_guard e base hc
    · intro low
      omega
    · intro _ flags
      apply eventually_trans (step e) (BodyPost {s with status := flags} bytes false base) _ _
      · exact false_body e base hc _ bytes
      · intro t post
        exact Eventually.done _ (post.preceded
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)
  | primitive shape =>
    have bound : Codec.descTag (.primitive shape) < 12 := by
      cases shape <;> decide
    apply bounded_dispatch e base hc s _ bound tag owned.table
    intro flags
    let prepared := jumped {s with status := flags} base (Codec.descTag (.primitive shape))
    apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.isFixed (.primitive shape)) base) _ _
    · cases shape <;> first | exact true_body e base hc prepared bytes | exact false_body e base hc prepared bytes
    · intro t post
      exact Eventually.done _ (post.preceded
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)
  | list element length =>
    apply bounded_dispatch e base hc s 8 (by decide) tag owned.table
    intro flags
    let prepared := jumped {s with status := flags} base 8
    apply eventually_trans (step e) (BodyPost prepared bytes false base) _ _
    · exact false_body e base hc prepared bytes
    · intro t post
      exact Eventually.done _ (post.preceded
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)
  | progressiveList element limit =>
    apply bounded_dispatch e base hc s 9 (by decide) tag owned.table
    intro flags
    let prepared := jumped {s with status := flags} base 9
    apply eventually_trans (step e) (BodyPost prepared bytes false base) _ _
    · exact false_body e base hc prepared bytes
    · intro t post
      exact Eventually.done _ (post.preceded
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)
  | container fields =>
    apply bounded_dispatch e base hc s 10 (by decide) tag owned.table
    intro flags
    let prepared := jumped {s with status := flags} base 10
    have owns : Working prepared base r (.container fields) bytes :=
      ⟨owned.descriptor, owned.table, owned.table_readonly, owned.stack,
        owned.enough, owned.above, owned.readonly⟩
    apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.fieldsFixed fields) base) _ _
    · exact container_body e base hc prepared r bytes fields
        (children fields (Or.inl rfl)) owns
    · intro t post
      exact Eventually.done _ (post.preceded
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)
  | progressiveContainer active fields =>
    apply bounded_dispatch e base hc s 11 (by decide) tag owned.table
    intro flags
    let prepared := jumped {s with status := flags} base 11
    have owns : Working prepared base r (.progressiveContainer active fields) bytes :=
      ⟨owned.descriptor, owned.table, owned.table_readonly, owned.stack,
        owned.enough, owned.above, owned.readonly⟩
    apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.fieldsFixed fields) base) _ _
    · exact progressive_body e base hc prepared r bytes active fields
        (children fields (Or.inr ⟨active, rfl⟩)) owns
    · intro t post
      exact Eventually.done _ (post.preceded
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)

end SszX86.CodecIsFixed
