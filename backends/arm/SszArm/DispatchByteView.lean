import SszArm.DispatchScalarOwned

namespace SszArm.Dispatch.Bytes

inductive Variant where
  | vector | list
  deriving DecidableEq

def Variant.kind : Variant → Kind
  | .vector => .byteVector | .list => .byteList

def Variant.schema (variant : Variant) (capacity : Nat) : Ssz.Desc :=
  match variant with | .vector => .byteVector capacity | .list => .byteList capacity

/-- The complete accepted body observation is retained, including aliasing of
empty input, arbitrary descriptor representation, and the saved activation.
The added frame and return fields relate directly to the original entry. -/
structure Post (s t : ArmState) (variant : Variant) (capacity : Nat) (data : Ssz.Bytes) : Prop where
  body : ByteView.Result (entered s variant.kind) t
    (Ssz.deserialize (variant.schema capacity) data) data
  pc : read_pc t = r (.GPR 30#5) s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg offset, (reg, offset) ∈ BoolCodec.savedRegisters → r (.GPR reg) t = r (.GPR reg) s
  frame : ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 384 ∨ (r (.GPR 31#5) s).toNat - 368 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
    t.mem a = s.mem a
  inputBytes : ∀ a : BitVec 64, (r (.GPR 2#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 2#5) s).toNat + data.size → t.mem a = s.mem a
  descriptorBytes : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + 24 → t.mem a = s.mem a

theorem post_of_body {s t : ArmState} {variant : Variant} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Scalar.Owned s variant.kind capacity data)
    (post : ByteView.Result (entered s variant.kind) t
      (Ssz.deserialize (variant.schema capacity) data) data) : Post s t variant capacity data := by
  have wholeFrame : ∀ a : BitVec 64,
      (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 384 ∨ (r (.GPR 31#5) s).toNat - 368 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
      t.mem a = s.mem a := by
    intro a out scratch activation
    apply (post.returned.frame a (by simpa using out) ?_).trans
      (entered_frame s variant.kind owned.entry.stackLow a activation)
    have low := owned.stackLow
    simp only [entered_sp, bodySP]
    bv_omega
  refine ⟨post, ?_, ?_, ?_, wholeFrame, ?_, ?_⟩
  · exact post.returned.pc.trans (by
      simpa only [entered_sp] using entered_saved s variant.kind owned.entry.stackLow 30#5 280 (by decide))
  · simpa only [entered_sp, bodySP, BitVec.sub_add_cancel] using post.returned.sp
  · intro reg offset member
    exact (post.returned.registers reg offset member).trans (by
      simpa only [entered_sp] using entered_saved s variant.kind owned.entry.stackLow reg offset member)
  · intro a low high
    have out := owned.inputOutput
    have stack := owned.inputStack
    apply wholeFrame a <;> omega
  · intro a low high
    have out := owned.descriptorOutput
    have stack := owned.descriptorStack
    apply wholeFrame a <;> omega

/-- Both real descriptor-tag paths execute from private entry PC0 through RET;
large and noncanonical capacities are passed to the accepted body unchanged. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (variant : Variant)
    (capacity : Nat) (data : Ssz.Bytes) (owned : Scalar.Owned s variant.kind capacity data)
    (dispatch : CodeAt s base) (body : ByteView.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t variant capacity data := by
  let b := entered s variant.kind
  have bodyCode : ByteView.CodeAt b base := by
    simpa only [b, ByteView.CodeAt, entered_program] using body
  have bodyError : read_err b = .None := by simpa only [b, entered_error] using error
  have bodyPC := entered_pc s base variant.kind owned.entry pc
  have decoded : ∃ fuel t, run fuel b = t ∧
      ByteView.Result b t (Ssz.deserialize (variant.schema capacity) data) data := by
    cases variant with
    | vector =>
      exact ByteView.Vector.runs b base capacity data bodyCode bodyPC bodyError
        (entered_aligned s _ aligned) owned.byte_owned
    | list =>
      exact ByteView.Bounded.runs b base capacity data bodyCode bodyPC bodyError
        (entered_aligned s _ aligned) owned.byte_owned
  obtain ⟨fuel, t, executed, post⟩ := decoded
  refine ⟨variant.kind.steps + fuel, t, ?_, post_of_body owned post⟩
  rw [run_plus, entry_run s base variant.kind owned.entry dispatch error aligned pc]
  exact executed

/-- Pinned SSZ result, original borrowed pointer even when empty, and the full
native frame are exposed together rather than erased by a value-only theorem. -/
theorem program_refines (s : ArmState) (base : BitVec 64) (variant : Variant)
    (capacity : Nat) (data : Ssz.Bytes) (owned : Scalar.Owned s variant.kind capacity data)
    (dispatch : CodeAt s base) (body : ByteView.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t variant capacity data ∧
      SszNative.ByteView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (variant.schema capacity) data) ∧
      (Ssz.deserialize (variant.schema capacity) data = .ok (.bytes data) →
        UintCodec.widthLoad t ((r (.GPR 0#5) s).toNat + 24) 8 = some (r (.GPR 2#5) s).toNat) := by
  obtain ⟨fuel, t, executed, post⟩ := program_correct s base variant capacity data owned
    dispatch body error aligned pc
  refine ⟨fuel, t, executed, post, ?_, ?_⟩
  · simpa using post.body.observed
  · simpa using post.body.aliases

end SszArm.Dispatch.Bytes
