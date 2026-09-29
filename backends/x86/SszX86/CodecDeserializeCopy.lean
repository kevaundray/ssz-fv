import SszX86.CodecDeserializeStorage
import SszX86.CodecStoragePlan

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative UintCodec

/-- Equality of observations after the six-word native Value copy. Equality of
Options does not assert that padding was initialized by semantic construction. -/
structure RootCopied (before after : DataMem) (source target : BitVec 64) : Prop where
  load : ∀ (offset bytes : Nat), offset + bytes ≤ 48 →
    Mem.loadInt after (target + BitVec.ofNat 64 offset) bytes =
      Mem.loadInt before (source + BitVec.ofNat 64 offset) bytes

private theorem copied_nat {m n : DataMem} {w : Codec.Footprint} {p q : BitVec 64}
    {number : NatOperand} (stored : Emit.NatAt m (p + 8) number)
    (copied : RootCopied m n p q) (frame : Codec.MemoryFrame m n w)
    (safe : ∀ a, Emit.NatBorrowed number a → ¬ w a) : Emit.NatAt n (q + 8) number := by
  refine ⟨?_, ?_, Codec.operand_frame number stored.2.2 frame safe⟩
  · have same : widthLoad n (q + 8).toNat 8 = widthLoad m (p + 8).toNat 8 := by
      unfold widthLoad
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [copied.load 8 8 (by decide)]
    exact same.trans stored.1
  · have same : widthLoad n ((q + 8).toNat + 8) 8 =
        widthLoad m ((p + 8).toNat + 8) 8 := by
      unfold widthLoad
      rw [width_address, width_address]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [copied.load 16 8 (by decide)]
    exact same.trans stored.2.1

private theorem copied_primitive {m n : DataMem} {r w : Codec.Footprint} {p q buffer : BitVec 64}
    {value : SszNative.Serialize.Value} (h : Codec.PrimitiveValueAt m r p buffer value)
    (copied : RootCopied m n p q) (span : Codec.Span r q 48 16)
    (frame : Codec.MemoryFrame m n w)
    (safe : ∀ a, Emit.ValueBorrowed value buffer a → ¬ w a) :
    Codec.PrimitiveValueAt n r q buffer value := by
  refine ⟨⟨?_, ?_⟩, span, h.borrowed⟩
  · have same : Mem.loadInt n q 1 = Mem.loadInt m p 1 := by
      simpa only [BitVec.ofNat_zero, BitVec.add_zero] using copied.load 0 1 (by decide)
    exact same.trans h.stored.1
  · have stored := h.stored.2
    cases value with
    | bool value => exact (copied.load 1 1 (by decide)).trans stored
    | uint number => exact copied_nat stored copied frame safe
    | bytes bytes =>
      refine ⟨(copied.load 8 8 (by decide)).trans stored.1,
        (copied.load 16 8 (by decide)).trans stored.2.1, ?_, stored.2.2.2⟩
      intro i hi
      rw [frame _ (safe _ ⟨i, hi, rfl⟩)]
      exact stored.2.2.1 i hi
    | bits bits =>
      refine ⟨(copied.load 16 8 (by decide)).trans stored.1,
        (copied.load 24 8 (by decide)).trans stored.2.1,
        (copied.load 32 8 (by decide)).trans stored.2.2.1,
        (copied.load 40 8 (by decide)).trans stored.2.2.2.1, ?_, stored.2.2.2.2.2⟩
      intro i hi
      rw [frame _ (safe _ ⟨i, hi, rfl⟩)]
      exact stored.2.2.2.2.1 i hi
    | seq _ | union _ _ => trivial

private theorem target_load_covered {r : Codec.Footprint} {q : BitVec 64}
    (span : Codec.Span r q 48 16) (off bytes : Nat) (bound : off + bytes ≤ 48) :
    ∀ a, Codec.InSpan a (q + BitVec.ofNat 64 off) bytes → r a :=
  fun a ha => span.covered a (Emit.span_shift q off bytes 48 bound ha)

private theorem target_nat_span {r : Codec.Footprint} {q : BitVec 64}
    (span : Codec.Span r q 48 16) : Codec.Span r (q + 8) 16 8 := by
  refine ⟨?_, ?_, ?_, target_load_covered span 8 16 (by decide)⟩
  · have := span.nonnull
    have := span.bound
    bv_omega
  · have := span.aligned
    have := span.bound
    bv_omega
  · have := span.bound
    bv_omega

/-- A returned child is installed at its actual arena address while all nested
children and borrowed bytes remain where the shared decoder model placed them.
The original root may be overwritten and the ambient footprint may contain it. -/
theorem nodeAt_relocate {m n : DataMem} {r w : Codec.Footprint} {source p q : BitVec 64}
    {node : CodecDecode.Node} (h : Codec.NodeAt m r source p node)
    (copied : RootCopied m n p q) (span : Codec.Span r q 48 16)
    (frame : Codec.MemoryFrame m n w)
    (safe : ∀ a, nodeBorrowed source node a → ¬ w a) : Codec.NodeAt n r source q node := by
  cases node with
  | bool value =>
    cases h with
    | bool primitive => exact .bool (copied_primitive primitive copied span frame safe)
  | uint number =>
    cases h with
    | uint primitive => exact .uint (copied_primitive primitive copied span frame safe)
  | bytes offset bytes =>
    cases h with
    | bytes bound primitive => exact .bytes bound (copied_primitive primitive copied span frame safe)
  | bits offset bits =>
    cases h with
    | bits bound primitive => exact .bits bound (copied_primitive primitive copied span frame safe)
  | seq allocation children =>
    cases h with
    | seq header bound empty slice childrenAt =>
      refine .seq ⟨span, ⟨?_, ?_⟩⟩ bound empty ?_ (nodesAt_frame childrenAt frame safe)
      · have same : Mem.loadInt n q 1 = Mem.loadInt m p 1 := by
          simpa only [BitVec.ofNat_zero, BitVec.add_zero] using copied.load 0 1 (by decide)
        exact same.trans header.tag.load
      · simpa only [BitVec.ofNat_zero, BitVec.add_zero] using target_load_covered span 0 1 (by decide)
      · refine ⟨⟨(copied.load 8 8 (by decide)).trans slice.pointer.load,
          target_load_covered span 8 8 (by decide)⟩, ⟨?_, ?_⟩,
          slice.countBound, slice.byteBound, slice.span⟩
        · have same : Mem.loadInt n (q + 8 + 8) 8 = Mem.loadInt m (p + 8 + 8) 8 := by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using copied.load 16 8 (by decide)
          exact same.trans slice.length.load
        · simpa only [BitVec.add_assoc, BitVec.reduceAdd] using target_load_covered span 16 8 (by decide)
  | union selector allocation child =>
    cases h with
    | union header bound number pointer childAt =>
      refine .union ⟨span, ⟨?_, ?_⟩⟩ bound
        ⟨copied_nat number.stored copied frame (fun a ha => safe a (Or.inl ha)),
          target_nat_span span, number.borrowed⟩
        ⟨(copied.load 24 8 (by decide)).trans pointer.load,
          target_load_covered span 24 8 (by decide)⟩
        (nodeAt_frame childAt frame (fun a ha => safe a (Or.inr ha)))
      · have same : Mem.loadInt n q 1 = Mem.loadInt m p 1 := by
          simpa only [BitVec.ofNat_zero, BitVec.add_zero] using copied.load 0 1 (by decide)
        exact same.trans header.tag.load
      · simpa only [BitVec.ofNat_zero, BitVec.add_zero] using target_load_covered span 0 1 (by decide)

end SszX86.CodecDeserialize
