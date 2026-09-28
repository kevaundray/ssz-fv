import SszX86.EmitBitsList

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open SszNative (NatOperand)

private theorem vector_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (length : NatOperand) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s (.bitVector length) bits src size) :
    Eventually (step e) (Post base s (.bitVector length) bits) (s, base + 672) := by
  apply vector_prepared e base hc s (.bitVector length) bits src size owned
  intro flags
  apply copy_prepared e base hc helper s (.bitVector length) bits src size owned false flags
  intro t copied
  exact vector_suffix e base hc s t length bits src size owned copied

private theorem list_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (kind : IsList desc) :
    Eventually (step e) (Post base s desc bits) (s, base + 428) := by
  apply list_prepared e base hc s desc bits src size owned
  intro flags
  apply copy_prepared e base hc helper s desc bits src size owned true flags
  intro t copied
  exact list_suffix e base hc s t desc bits src size owned kind copied

private def routed (s : MachineData) (rcx : UInt64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rcx}, status := flags}

private theorem owned_routed {s : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} (owned : Owned s desc bits src size)
    (rcx : UInt64) (flags : StatusFlags) : Owned (routed s rcx flags) desc bits src size :=
  ⟨owned.kind, owned.valid, owned.tag, owned.physical, owned.pointer, owned.length,
    owned.low, owned.high, owned.source, owned.outputMapped, owned.resultMapped,
    owned.stackMapped, owned.outputResult, owned.outputStack, owned.resultStack,
    owned.headerProtected, owned.sourceProtected⟩

private theorem post_routed {s t : MachineData} {bytes : Ssz.Bytes} {rcx : UInt64}
    {flags : StatusFlags} (post : BodyPost (routed s rcx flags) bytes t) : BodyPost s bytes t :=
  ⟨post.stack, post.result, post.length, post.output, post.frame, post.vector⟩

private theorem routed_execution (e : Executable) (base : Int64) (s : MachineData)
    (desc : Desc) (bits : Packed) (rcx : UInt64) (flags : StatusFlags) (pc : Int64)
    (execution : Eventually (step e) (Post base (routed s rcx flags) desc bits)
      (routed s rcx flags, pc)) :
    Eventually (step e) (Post base s desc bits) (routed s rcx flags, pc) := by
  apply eventually_weaken (step e) _ _ _ _ execution
  intro t post
  exact ⟨post.1, post_routed post.2⟩

/-- Actual PC414→PC1593 execution for all three primitive bit descriptors.
Every branch, backing access and memcpy resource is derived from successful
logical expectedSize, the original physical Packed representation and incoming
output/result/stack ownership. Logical caps may have arbitrary padded native
Nat representations, and a progressive cap may be absent. Dirty packed high
padding is accepted. No future guard, callee exit, or execution is a premise. -/
theorem body_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) :
    Eventually (step e) (Post base s desc bits) (s, base + 414) := by
  cases desc with
  | bitVector length =>
    apply route_vector e base hc s owned.tag
    intro flags
    exact routed_execution e base s (.bitVector length) bits 18446744073709551615 flags _
      (vector_body e base hc helper _ length bits src size (owned_routed owned _ flags))
  | bitList limit =>
    apply route_list e base hc s 5 (Or.inl rfl) owned.tag
    intro flags
    exact routed_execution e base s (.bitList limit) bits 0 flags _
      (list_body e base hc helper _ (.bitList limit) bits src size (owned_routed owned _ flags) trivial)
  | progressiveBitList limit =>
    apply route_list e base hc s 6 (Or.inr rfl) owned.tag
    intro flags
    exact routed_execution e base s (.progressiveBitList limit) bits 1 flags _
      (list_body e base hc helper _ (.progressiveBitList limit) bits src size
        (owned_routed owned _ flags) trivial)
  | bool => cases owned.kind
  | uint _ => cases owned.kind
  | byteVector _ => cases owned.kind
  | byteList _ => cases owned.kind

/-- The endpoint bytes are the pinned serializer's exact result, with the
physical length and byte frame supplied by BodyPost. Original-entry dispatch
and the common success store/epilogue are composed by the emitter coordinator. -/
theorem body_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) :
    Eventually (step e) (fun t => Post base s desc bits t ∧
      Ssz.serialize desc.erase (SszNative.Serialize.Value.bits bits).erase =
        .ok (SszNative.Serialize.emit desc (.bits bits)) ∧
      (SszNative.Serialize.emit desc (.bits bits)).size = size) (s, base + 414) := by
  apply eventually_weaken (step e) _ _ _ _ (body_correct e base hc helper s desc bits src size owned)
  intro t post
  exact ⟨post, owned.valid.pinned, owned.valid.emitted_size⟩

end SszX86.Emit.Bits
