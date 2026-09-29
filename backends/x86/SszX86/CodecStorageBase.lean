import SszX86.EmitOwnedMemory
import SszCodecMeasure
import SszCodecDecodeCore

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

abbrev Footprint := BitVec 64 → Prop
abbrev InSpan := Emit.InSpan
abbrev MemoryFrame := Emit.MemoryFrame

/-- A physical borrowed span. This does not assert that its padding is initialized.
Readonly spans may overlap, including complete sharing of recursive children. -/
structure Span (readable : Footprint) (p : BitVec 64) (bytes alignment : Nat) : Prop where
  nonnull : 0 < p.toNat
  aligned : p.toNat % alignment = 0
  bound : p.toNat + bytes ≤ 2 ^ 64
  covered : ∀ a, InSpan a p bytes → readable a

/-- Only the bytes of an actual observation need to be initialized. -/
structure LoadAt (m : DataMem) (readable : Footprint) (p : BitVec 64)
    (bytes : Nat) (value : Int) : Prop where
  «load» : Mem.loadInt m p bytes = some value
  covered : ∀ a, InSpan a p bytes → readable a

theorem LoadAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {bytes : Nat} {value : Int} (h : LoadAt m r p bytes value)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    LoadAt n r p bytes value := by
  refine ⟨?_, h.covered⟩
  rw [Emit.frame_load m n w frame p bytes]
  · exact h.load
  · intro i hi
    exact separate _ (h.covered _ ⟨i, hi, rfl⟩)

structure NatAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (value : NatOperand) : Prop where
  stored : Emit.NatAt m p value
  span : Span r p 16 8
  borrowed : ∀ a, Emit.NatBorrowed value a → r a

theorem NatAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {value : NatOperand} (h : NatAt m r p value)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    NatAt n r p value :=
  ⟨Emit.natAt_frame m n w frame p value
    (fun a ha => separate a (h.span.covered a ha))
    (fun a ha => separate a (h.borrowed a ha)) h.stored, h.span, h.borrowed⟩

structure BytesAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (bytes : Ssz.Bytes) : Prop where
  stored : Emit.BytesAt m p bytes
  span : Span r p bytes.size 1

theorem BytesAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {bytes : Ssz.Bytes} (h : BytesAt m r p bytes)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    BytesAt n r p bytes := by
  refine ⟨?_, h.span⟩
  intro i hi
  rw [frame _ (separate _ (h.span.covered _ ⟨i, hi, rfl⟩))]
  exact h.stored i hi

/-- A fat pointer uses actual host-sized length, not a logical Nat bound. -/
structure SliceAt (m : DataMem) (r : Footprint) (field buffer : BitVec 64)
    (count stride alignment : Nat) : Prop where
  pointer : LoadAt m r field 8 (buffer.toNat : Int)
  length : LoadAt m r (field + 8) 8 (count : Int)
  countBound : count < 2 ^ 64
  /-- Rust's physical slice byte size is at most isize::MAX. -/
  byteBound : stride * count < 2 ^ 63
  span : Span r buffer (stride * count) alignment

theorem SliceAt.frame {m n : DataMem} {r w : Footprint} {field buffer : BitVec 64}
    {count stride alignment : Nat} (h : SliceAt m r field buffer count stride alignment)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    SliceAt n r field buffer count stride alignment :=
  ⟨h.pointer.frame frame separate, h.length.frame frame separate, h.countBound,
    h.byteBound, h.span⟩

/-- Reuse the primitive ABI relation without weakening recursive storage to tags. -/
structure PrimitiveDescAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (desc : SszNative.Serialize.Desc) : Prop where
  stored : Emit.DescAt m p desc
  span : Span r p 40 8
  borrowed : ∀ a, Emit.DescBorrowed desc a → r a

structure PrimitiveValueAt (m : DataMem) (r : Footprint) (p buffer : BitVec 64)
    (value : SszNative.Serialize.Value) : Prop where
  stored : Emit.ValueAt m p buffer value
  span : Span r p 48 16
  borrowed : ∀ a, Emit.ValueBorrowed value buffer a → r a

private theorem load_frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {total alignment : Nat} (span : Span r p total alignment)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a)
    (off bytes : Nat) (bound : off + bytes ≤ total) :
    Mem.loadInt n (p + BitVec.ofNat 64 off) bytes =
      Mem.loadInt m (p + BitVec.ofNat 64 off) bytes := by
  apply Emit.frame_load m n w frame
  intro i hi
  exact separate _ (span.covered _ (Emit.span_shift p off bytes total bound ⟨i, hi, rfl⟩))

private theorem nat_frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {total alignment : Nat} (span : Span r p total alignment)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a)
    (off : Nat) (bound : off + 16 ≤ total) (operand : NatOperand)
    (borrowed : ∀ a, Emit.NatBorrowed operand a → r a)
    (stored : Emit.NatAt m (p + BitVec.ofNat 64 off) operand) :
    Emit.NatAt n (p + BitVec.ofNat 64 off) operand :=
  Emit.natAt_frame m n w frame _ operand
    (fun a ha => separate a (span.covered a (Emit.span_shift p off 16 total bound ha)))
    (fun a ha => separate a (borrowed a ha)) stored

theorem PrimitiveDescAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {desc : SszNative.Serialize.Desc} (h : PrimitiveDescAt m r p desc)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    PrimitiveDescAt n r p desc := by
  refine ⟨⟨?_, ?_⟩, h.span, h.borrowed⟩
  · have same : Mem.loadInt n p 8 = Mem.loadInt m p 8 := by
      simpa only [BitVec.add_zero] using load_frame h.span frame separate 0 8 (by decide)
    exact same.trans h.stored.1
  · have stored := h.stored.2
    have borrowed := h.borrowed
    cases desc with
    | bool => trivial
    | uint operand | byteVector operand | byteList operand
    | bitVector operand | bitList operand =>
      exact nat_frame h.span frame separate 8 (by decide) operand borrowed stored
    | progressiveBitList limit =>
      cases limit with
      | none => exact (load_frame h.span frame separate 8 4 (by decide)).trans stored
      | some operand =>
        exact ⟨(load_frame h.span frame separate 8 4 (by decide)).trans stored.1,
          nat_frame h.span frame separate 16 (by decide) operand borrowed stored.2⟩

theorem PrimitiveValueAt.frame {m n : DataMem} {r w : Footprint} {p buffer : BitVec 64}
    {value : SszNative.Serialize.Value} (h : PrimitiveValueAt m r p buffer value)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    PrimitiveValueAt n r p buffer value := by
  refine ⟨⟨?_, ?_⟩, h.span, h.borrowed⟩
  · have same : Mem.loadInt n p 1 = Mem.loadInt m p 1 := by
      simpa only [BitVec.add_zero] using load_frame h.span frame separate 0 1 (by decide)
    exact same.trans h.stored.1
  · have stored := h.stored.2
    have borrowed := h.borrowed
    cases value with
    | bool value => exact (load_frame h.span frame separate 1 1 (by decide)).trans stored
    | uint number => exact nat_frame h.span frame separate 8 (by decide) number borrowed stored
    | bytes bytes =>
      refine ⟨(load_frame h.span frame separate 8 8 (by decide)).trans stored.1,
        (load_frame h.span frame separate 16 8 (by decide)).trans stored.2.1,
        ?_, stored.2.2.2⟩
      intro i hi
      rw [frame _ (separate _ (borrowed _ ⟨i, hi, rfl⟩))]
      exact stored.2.2.1 i hi
    | bits bits =>
      refine ⟨(load_frame h.span frame separate 16 8 (by decide)).trans stored.1,
        (load_frame h.span frame separate 24 8 (by decide)).trans stored.2.1,
        (load_frame h.span frame separate 32 8 (by decide)).trans stored.2.2.1,
        (load_frame h.span frame separate 40 8 (by decide)).trans stored.2.2.2.1,
        ?_, stored.2.2.2.2.2⟩
      intro i hi
      rw [frame _ (separate _ (borrowed _ ⟨i, hi, rfl⟩))]
      exact stored.2.2.2.2.1 i hi
    | seq _ | union _ _ => trivial

/-- The native Option<Nat> tag is a u32; inactive bytes are unconstrained. -/
inductive OptionNatAt (m : DataMem) (r : Footprint) (p : BitVec 64) :
    Option NatOperand → Prop where
  | none : LoadAt m r p 4 0 → OptionNatAt m r p none
  | some {operand : NatOperand} : LoadAt m r p 4 1 → NatAt m r (p + 8) operand →
      OptionNatAt m r p (some operand)

theorem OptionNatAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {value : Option NatOperand} (h : OptionNatAt m r p value)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    OptionNatAt n r p value := by
  cases h with
  | none tag => exact .none (tag.frame frame separate)
  | some tag operand => exact .some (tag.frame frame separate) (operand.frame frame separate)

end SszX86.Codec
