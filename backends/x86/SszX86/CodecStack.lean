import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

/-- Actual prologue allocations in /tmp/ssz-codec-linked.json, including PUSHes.
A CALL's eight-byte return slot and its callee's demand are additional. -/
inductive StackRoutine where
  | serialize | measure | emit | deserialize | measureParts | measureChild | emitParts
  | isFixed | measureFixed | decodeFixed | decodeOffsets | decodeList | readOffset
  | bounded | natCmpUsize | planSingleton | decodeStructValues
  deriving DecidableEq

def activationBytes : StackRoutine → Nat
  | .serialize => 136
  | .measure => 264
  | .emit => 152
  | .deserialize => 360
  | .measureParts => 376
  | .measureChild => 216
  | .emitParts => 200
  | .isFixed => 24
  | .measureFixed => 136
  | .decodeFixed => 312
  | .decodeOffsets => 344
  | .decodeList => 152
  | .readOffset => 8
  | .bounded => 40
  | .natCmpUsize | .planSingleton => 0
  | .decodeStructValues => 344

def callBytes (routine : StackRoutine) (calleeBytes : Nat) : Nat :=
  activationBytes routine + 8 + calleeBytes

/-- One layer reserves each codec activation and its CALL slot. This is a
compositional allowance, not an assertion that any particular call occurs. Native
Nat/memory/lowering helpers must be included separately by their checked provider. -/
def codecLayerBytes : Nat :=
  136 + 264 + 152 + 360 + 376 + 216 + 200 + 24 + 136 + 312 + 344 + 152 + 8 + 40 + 0 + 0 + 344 + 17 * 8

theorem activation_with_call_le_layer (routine : StackRoutine) :
    activationBytes routine + 8 ≤ codecLayerBytes := by
  cases routine <;> decide

/-- Depth counts recursive declarations only; neither Nat magnitudes nor schema
validity occur in this resource bound. Helper scratch is a separate allowance. -/
def recursiveStackBytes (depth helperBytes : Nat) : Nat :=
  depth * codecLayerBytes + helperBytes

def descriptorStackBytes (desc : SszNative.Codec.Desc) (helperBytes : Nat) : Nat :=
  recursiveStackBytes (desc.nesting + 1) helperBytes

theorem recursiveStackBytes_child (parentDepth childDepth helperBytes consumed : Nat)
    (descends : childDepth < parentDepth) (layer : consumed ≤ codecLayerBytes) :
    consumed + recursiveStackBytes childDepth helperBytes ≤
      recursiveStackBytes parentDepth helperBytes := by
  have levels := Nat.mul_le_mul_right codecLayerBytes (Nat.succ_le_of_lt descends)
  simp only [Nat.succ_mul] at levels
  unfold recursiveStackBytes
  omega

theorem recursiveStackBytes_helper (depth helperBytes : Nat) :
    helperBytes ≤ recursiveStackBytes depth helperBytes := by
  unfold recursiveStackBytes
  omega

/-- Ownership of an arbitrary finite downward-growing region; there is no leaf
budget baked into the recursive caller's precondition. The caller return slot at
`sp` is not writable in this region. -/
structure StackAt (m : DataMem) (sp : BitVec 64) (bytes : Nat) : Prop where
  lowEnough : bytes ≤ sp.toNat
  «mapped» : Large.Mapped m (sp - BitVec.ofNat 64 bytes) bytes

def StackWrites (sp : BitVec 64) (bytes : Nat) : Footprint :=
  fun a => InSpan a (sp - BitVec.ofNat 64 bytes) bytes

/-- A nested helper's complete region is inside its caller's original allowance. -/
theorem stack_subspan (sp : BitVec 64) (consumed child total : Nat)
    (within : consumed + child ≤ total) (a : BitVec 64)
    (inside : StackWrites (sp - BitVec.ofNat 64 consumed) child a) :
    StackWrites sp total a := by
  have pointer : sp - BitVec.ofNat 64 consumed - BitVec.ofNat 64 child =
      (sp - BitVec.ofNat 64 total) + BitVec.ofNat 64 (total - consumed - child) := by
    bv_omega
  unfold StackWrites at inside ⊢
  rw [pointer] at inside
  exact Emit.span_shift _ (total - consumed - child) child total (by omega) inside

theorem StackAt.substack {m : DataMem} {sp : BitVec 64} {total : Nat}
    (h : StackAt m sp total) (consumed child : Nat) (within : consumed + child ≤ total) :
    StackAt m (sp - BitVec.ofNat 64 consumed) child := by
  have low := h.lowEnough
  refine ⟨by bv_omega, ?_⟩
  have mapped := Delimited.Reservation.mapped_subrange m (sp - BitVec.ofNat 64 total)
    total (total - consumed - child) child h.mapped (by omega)
  have pointer : (sp - BitVec.ofNat 64 total) + BitVec.ofNat 64 (total - consumed - child) =
      sp - BitVec.ofNat 64 consumed - BitVec.ofNat 64 child := by
    bv_omega
  rw [pointer] at mapped
  exact mapped

theorem StackAt.call {m : DataMem} {sp : BitVec 64} {total : Nat}
    (h : StackAt m sp total) (routine : StackRoutine) (child : Nat)
    (within : callBytes routine child ≤ total) :
    StackAt m (sp - BitVec.ofNat 64 (activationBytes routine + 8)) child :=
  h.substack (activationBytes routine + 8) child within

/-- The existing six-save primitive image is valid for every larger recursive
frame, rather than only its historical 160-byte emitter budget. -/
theorem savedSix_frame (s : MachineData) (bytes : Nat) (enough : 48 ≤ bytes) :
    MemoryFrame s.dmem (Emit.savedMem s) (StackWrites s.regs.rsp.toBitVec bytes) := by
  intro a outside
  apply Dispatch.saved_lookup s a
  intro i hi equal
  apply outside
  apply stack_subspan s.regs.rsp.toBitVec 0 48 bytes (by omega) a
  change InSpan a (s.regs.rsp.toBitVec - 48) 48
  exact ⟨i, hi, equal⟩

theorem Stored.savedSix {s : MachineData} {r : Footprint} {object : StorageObject}
    (h : Stored s.dmem r object) (bytes : Nat) (enough : 48 ≤ bytes)
    (readonly : ∀ a, r a → ¬ StackWrites s.regs.rsp.toBitVec bytes a) :
    Stored (Emit.savedMem s) r object :=
  h.frame (savedSix_frame s bytes enough) readonly

/-- Byte-exact outside-frame preservation composes across differently sized helper
activations, including helpers whose scratch demand exceeds their caller's locals. -/
theorem MemoryFrame.trans {m n o : DataMem} {left right : Footprint}
    (first : MemoryFrame m n left) (second : MemoryFrame n o right) :
    MemoryFrame m o (fun a => left a ∨ right a) := by
  intro a outside
  exact (second a (fun h => outside (Or.inr h))).trans
    (first a (fun h => outside (Or.inl h)))

end SszX86.Codec
