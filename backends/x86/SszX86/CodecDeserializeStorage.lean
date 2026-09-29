import SszX86.CodecStorageDecode

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative

mutual
  /-- Concrete initialized-node storage and its actual borrowed payload, not
  the ambient memory region used when the node was constructed. -/
  def nodeFootprint (source p : BitVec 64) : CodecDecode.Node → Codec.Footprint
    | .bool _ => fun a => Codec.InSpan a p 48
    | .uint number => fun a => Codec.InSpan a p 48 ∨ Emit.NatBorrowed number a
    | .bytes offset bytes => fun a => Codec.InSpan a p 48 ∨
        Codec.InSpan a (source + BitVec.ofNat 64 offset) bytes.size
    | .bits offset bits => fun a => Codec.InSpan a p 48 ∨
        Codec.InSpan a (source + BitVec.ofNat 64 offset) bits.bytes.size
    | .seq allocation children => fun a => Codec.InSpan a p 48 ∨
        nodesFootprint source (BitVec.ofNat 64 (Codec.decodedChildrenPointer allocation)) children a
    | .union selector allocation child => fun a => Codec.InSpan a p 48 ∨
        Emit.NatBorrowed selector a ∨ nodeFootprint source (BitVec.ofNat 64 allocation.pointer) child a

  def nodesFootprint (source p : BitVec 64) : List CodecDecode.Node → Codec.Footprint
    | [] => fun _ => False
    | node :: rest => fun a => nodeFootprint source p node a ∨ nodesFootprint source (p + 48) rest a
end

/-- Excluding the copied outer record still protects all descendants and Nat
limbs. Readonly aliases amongst those descendants remain legal. -/
def nodeBorrowed (source : BitVec 64) : CodecDecode.Node → Codec.Footprint
  | .bool _ => fun _ => False
  | .uint number => Emit.NatBorrowed number
  | .bytes offset bytes => fun a => Codec.InSpan a (source + BitVec.ofNat 64 offset) bytes.size
  | .bits offset bits => fun a => Codec.InSpan a (source + BitVec.ofNat 64 offset) bits.bytes.size
  | .seq allocation children =>
      nodesFootprint source (BitVec.ofNat 64 (Codec.decodedChildrenPointer allocation)) children
  | .union selector allocation child => fun a => Emit.NatBorrowed selector a ∨
      nodeFootprint source (BitVec.ofNat 64 allocation.pointer) child a

theorem loadAt_frame {m n : DataMem} {r w : Codec.Footprint} {p : BitVec 64}
    {bytes : Nat} {value : Int} (h : Codec.LoadAt m r p bytes value)
    (frame : Codec.MemoryFrame m n w)
    (safe : ∀ a, Codec.InSpan a p bytes → ¬ w a) : Codec.LoadAt n r p bytes value := by
  refine ⟨?_, h.covered⟩
  rw [Emit.frame_load m n w frame p bytes (fun i hi => safe _ ⟨i, hi, rfl⟩)]
  exact h.load

theorem headerAt_frame {m n : DataMem} {r w : Codec.Footprint} {p : BitVec 64}
    {bytes alignment tagBytes : Nat} {tag : Int}
    (h : Codec.HeaderAt m r p bytes alignment tagBytes tag)
    (fits : tagBytes ≤ bytes) (frame : Codec.MemoryFrame m n w)
    (safe : ∀ a, Codec.InSpan a p bytes → ¬ w a) :
    Codec.HeaderAt n r p bytes alignment tagBytes tag := by
  refine ⟨h.span, loadAt_frame h.tag frame ?_⟩
  rintro a ⟨i, hi, equal⟩
  exact safe a ⟨i, Nat.lt_of_lt_of_le hi fits, equal⟩

theorem natAt_frame {m n : DataMem} {r w : Codec.Footprint} {p : BitVec 64}
    {number : NatOperand} (h : Codec.NatAt m r p number)
    (frame : Codec.MemoryFrame m n w)
    (header : ∀ a, Codec.InSpan a p 16 → ¬ w a)
    (limbs : ∀ a, Emit.NatBorrowed number a → ¬ w a) : Codec.NatAt n r p number :=
  ⟨Emit.natAt_frame m n w frame p number header limbs h.stored, h.span, h.borrowed⟩

theorem sliceAt_frame {m n : DataMem} {r w : Codec.Footprint} {p buffer : BitVec 64}
    {count stride alignment : Nat} (h : Codec.SliceAt m r p buffer count stride alignment)
    (frame : Codec.MemoryFrame m n w)
    (safe : ∀ a, Codec.InSpan a p 16 → ¬ w a) :
    Codec.SliceAt n r p buffer count stride alignment := by
  refine ⟨loadAt_frame h.pointer frame ?_, loadAt_frame h.length frame ?_,
    h.countBound, h.byteBound, h.span⟩
  · rintro a ⟨i, hi, equal⟩
    exact safe a ⟨i, by omega, equal⟩
  · intro a ha
    exact safe a (Emit.span_shift p 8 8 16 (by decide) ha)

theorem primitiveAt_frame {m n : DataMem} {r w : Codec.Footprint} {p buffer : BitVec 64}
    {value : SszNative.Serialize.Value} (h : Codec.PrimitiveValueAt m r p buffer value)
    (frame : Codec.MemoryFrame m n w)
    (header : ∀ a, Codec.InSpan a p 48 → ¬ w a)
    (borrowed : ∀ a, Emit.ValueBorrowed value buffer a → ¬ w a) :
    Codec.PrimitiveValueAt n r p buffer value := by
  let precise : Codec.Footprint := fun a => Codec.InSpan a p 48 ∨ Emit.ValueBorrowed value buffer a
  have narrowed : Codec.PrimitiveValueAt m precise p buffer value :=
    ⟨h.stored, ⟨h.span.nonnull, h.span.aligned, h.span.bound, fun _ ha => Or.inl ha⟩,
      fun _ ha => Or.inr ha⟩
  have kept := narrowed.frame frame (fun a ha => ha.elim (header a) (borrowed a))
  exact ⟨kept.stored, h.span, h.borrowed⟩

mutual
  /-- Ambient footprints can include mutable stack/output. Preservation uses
  only this node's concrete recursive storage, not every byte of that ambient set. -/
  theorem nodeAt_frame {m n : DataMem} {r w : Codec.Footprint} {source p : BitVec 64}
      {node : CodecDecode.Node} (h : Codec.NodeAt m r source p node)
      (frame : Codec.MemoryFrame m n w)
      (safe : ∀ a, nodeFootprint source p node a → ¬ w a) : Codec.NodeAt n r source p node := by
    cases node with
    | bool value =>
      cases h with
      | bool primitive =>
        exact .bool (primitiveAt_frame primitive frame safe (by intro a impossible; cases impossible))
    | uint number =>
      cases h with
      | uint primitive =>
        exact .uint (primitiveAt_frame primitive frame
          (fun a ha => safe a (Or.inl ha)) (fun a ha => safe a (Or.inr ha)))
    | bytes offset bytes =>
      cases h with
      | bytes bound primitive =>
        exact .bytes bound (primitiveAt_frame primitive frame
          (fun a ha => safe a (Or.inl ha)) (fun a ha => safe a (Or.inr ha)))
    | bits offset bits =>
      cases h with
      | bits bound primitive =>
        exact .bits bound (primitiveAt_frame primitive frame
          (fun a ha => safe a (Or.inl ha)) (fun a ha => safe a (Or.inr ha)))
    | seq allocation children =>
      cases h with
      | seq header bound empty slice childrenAt =>
        refine .seq (headerAt_frame header (by decide) frame (fun a ha => safe a (Or.inl ha)))
          bound empty (sliceAt_frame slice frame ?_) (nodesAt_frame childrenAt frame ?_)
        · intro a ha
          exact safe a (Or.inl (Emit.span_shift p 8 16 48 (by decide) ha))
        · intro a ha
          exact safe a (Or.inr ha)
    | union selector allocation child =>
      cases h with
      | union header bound number pointer childAt =>
        refine .union (headerAt_frame header (by decide) frame (fun a ha => safe a (Or.inl ha)))
          bound (natAt_frame number frame ?_ ?_) (loadAt_frame pointer frame ?_)
          (nodeAt_frame childAt frame ?_)
        · intro a ha
          exact safe a (Or.inl (Emit.span_shift p 8 16 48 (by decide) ha))
        · intro a ha
          exact safe a (Or.inr (Or.inl ha))
        · intro a ha
          exact safe a (Or.inl (Emit.span_shift p 24 8 48 (by decide) ha))
        · intro a ha
          exact safe a (Or.inr (Or.inr ha))
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  theorem nodesAt_frame {m n : DataMem} {r w : Codec.Footprint} {source p : BitVec 64}
      {nodes : List CodecDecode.Node} (h : Codec.NodesAt m r source p nodes)
      (frame : Codec.MemoryFrame m n w)
      (safe : ∀ a, nodesFootprint source p nodes a → ¬ w a) : Codec.NodesAt n r source p nodes := by
    cases nodes with
    | nil => exact .nil
    | cons node rest =>
      cases h with
      | cons head tail =>
        exact .cons (nodeAt_frame head frame (fun a ha => safe a (Or.inl ha)))
          (nodesAt_frame tail frame (fun a ha => safe a (Or.inr ha)))
  termination_by sizeOf nodes
  decreasing_by all_goals simp_wf <;> omega
end

end SszX86.CodecDeserialize
