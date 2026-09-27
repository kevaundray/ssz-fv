import SszArm.DelimitedImpl
import SszArm.UintWidthMemory
import SszArm.BoolResultMemory
import SszBitView
import SszNatABI

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

abbrev Span := Nat × Nat

/-- Empty spans are vacuous. Immutable spans may overlap each other and the
already-used arena prefix; only actual writable intervals require separation. -/
def Protected (writes : List Span) (address bytes : Nat) : Prop :=
  bytes = 0 ∨ ∀ span ∈ writes,
    address + bytes ≤ span.1 ∨ span.1 + span.2 ≤ address

def MemoryFrame (writes : List Span) (s t : ArmState) : Prop :=
  ∀ a : BitVec 64,
    (∀ span ∈ writes, a.toNat < span.1 ∨ span.1 + span.2 ≤ a.toNat) →
    t.mem a = s.mem a

theorem MemoryFrame.refl (writes : List Span) (s : ArmState) :
    MemoryFrame writes s s := fun _ _ => rfl

theorem MemoryFrame.trans {writes : List Span} {s t u : ArmState}
    (st : MemoryFrame writes s t) (tu : MemoryFrame writes t u) :
    MemoryFrame writes s u := fun a ha => (tu a ha).trans (st a ha)

theorem MemoryFrame.load {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (address bytes : Nat)
    (physical : address + bytes ≤ 2^64) (owned : Protected writes address bytes) :
    widthLoad t address bytes = widthLoad s address bytes := by
  unfold widthLoad
  congr 1
  congr 1
  apply BoolCodec.read_bytes_congr
  intro i hi
  change t.mem _ = s.mem _
  apply frame
  intro span hspan
  rcases owned with empty | separate
  · omega
  · have hsep := separate span hspan
    bv_omega

def NatOwned (writes : List Span) (pointer payload : BitVec 64) : Prop :=
  pointer ≠ 0#64 → payload ≠ 0#64 → Protected writes pointer.toNat (8 * payload.toNat)

theorem MemoryFrame.pair {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (pointer payload : BitVec 64) (value : Nat)
    (pair : SszNative.NatMemory.Pair (widthLoad s) pointer payload value)
    (owned : NatOwned writes pointer payload) :
    SszNative.NatMemory.Pair (widthLoad t) pointer payload value := by
  rcases pair with small | ⟨words, positive, aligned, physical, count, limbs, valueEq⟩
  · exact Or.inl small
  · refine Or.inr ⟨words, positive, aligned, physical, count, ?_, valueEq⟩
    intro i
    have hi := i.isLt
    have nonzero : pointer ≠ 0#64 := by intro h; simp [h] at positive
    have countNonzero : payload ≠ 0#64 := by
      intro h
      have : words.length = 0 := by simpa [h] using count.symm
      omega
    have hprotected := owned nonzero countNonzero
    rw [count] at hprotected
    have wordOwned : Protected writes (pointer.toNat + 8 * i.val) 8 := by
      right
      intro span hspan
      rcases hprotected with empty | separate
      · omega
      · have hsep := separate span hspan
        omega
    rw [frame.load _ _ (by omega) wordOwned]
    exact limbs i


/-- The exact callee writable activation: the empty path uses only its 16-byte
lowering slot; every nonempty path has 96 saved bytes plus a lower 16-byte slot. -/
def activationSpan (s : ArmState) : Span :=
  let bytes := if r (.GPR 3#5) s = 0#64 then 16 else 112
  ((r (.GPR 31#5) s).toNat - bytes, bytes)

def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 76), activationSpan s]

/-- Only the arena cursor field and exactly sixteen fresh limb bytes are added
on allocation success. Alignment padding is not written. -/
def allocatedWrites (s : ArmState) (pointer : Nat) : List Span :=
  localWrites s ++ [((r (.GPR 4#5) s).toNat + 16, 8), (pointer, 16)]

structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

/-- Store preservation is usable one instruction at a time, without unfolding
the entire decoder state. -/
theorem store_frame (s : ArmState) (address : BitVec 64) (bytes : Nat)
    (value : BitVec (bytes * 8)) (physical : address.toNat + bytes ≤ 2^64) :
    MemoryFrame [(address.toNat, bytes)] s (write_mem_bytes bytes address value s) := by
  intro a ha
  exact BoolCodec.write_mem_bytes_frame s address bytes value a physical
    (ha (address.toNat, bytes) (by simp))

end SszArm.Delimited
