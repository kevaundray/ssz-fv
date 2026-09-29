import SszArm.IndicesLinkedNatShr
import SszArm.CodecStorageBase
import SszNatShift

set_option autoImplicit false

namespace SszArm.Indices.NatShr.Counterexample

open SszNative (NatOperand)

/-- The linked image, at its actual ELF address, without replacing any word. -/
def code : Program :=
  Linked.NatShr.program.map fun row =>
    (BitVec.ofNat 64 Linked.NatShr.address + BitVec.ofNat 64 row.1, row.2)

/-- A mapped, aligned two-limb input. Its mathematical value is 2 * 2^64 + 5. -/
def operand : NatOperand := .large 8192#64 [5#64, 2#64]

/-- Concrete original-entry state. Output, input, input header, arena descriptor,
backing storage and the lower stack slot are pairwise disjoint. The u128 shift
is passed in x4/x5, not in the skipped x3 argument register. -/
def initial : ArmState :=
  let s := set_program ArmState.default code
  let s := write_mem_bytes 8 8192#64 5#64 s
  let s := write_mem_bytes 8 8200#64 2#64 s
  let s := write_mem_bytes 8 8448#64 8192#64 s
  let s := write_mem_bytes 8 8456#64 2#64 s
  let s := write_mem_bytes 8 12288#64 20480#64 s
  let s := write_mem_bytes 8 12296#64 256#64 s
  let s := write_mem_bytes 8 12304#64 0#64 s
  let s := w (.GPR 0#5) 4096#64 s
  let s := w (.GPR 1#5) 8192#64 s
  let s := w (.GPR 2#5) 2#64 s
  let s := w (.GPR 4#5) 64#64 s
  let s := w (.GPR 5#5) 0#64 s
  let s := w (.GPR 6#5) 12288#64 s
  let s := w (.GPR 30#5) 16384#64 s
  let s := w (.GPR 31#5) 32768#64 s
  w .PC (BitVec.ofNat 64 Linked.NatShr.address) s

private def codeCheck (rows : List (Nat × BitVec 32)) : Bool :=
  rows.all fun row => decide
    (code.find? (BitVec.ofNat 64 Linked.NatShr.address + BitVec.ofNat 64 row.1) =
      some row.2)

private theorem code0 : codeCheck Linked.NatShr.chunk0 = true := by decide
private theorem code1 : codeCheck Linked.NatShr.chunk1 = true := by decide
private theorem code2 : codeCheck Linked.NatShr.chunk2 = true := by decide
private theorem code3 : codeCheck Linked.NatShr.chunk3 = true := by decide
private theorem code4 : codeCheck Linked.NatShr.chunk4 = true := by decide
private theorem code5 : codeCheck Linked.NatShr.chunk5 = true := by decide

theorem original_code :
    Linked.NatShr.CodeAt initial (BitVec.ofNat 64 Linked.NatShr.address) := by
  have checked : codeCheck Linked.NatShr.program = true := by
    have h0 := code0
    have h1 := code1
    have h2 := code2
    have h3 := code3
    have h4 := code4
    have h5 := code5
    simp only [codeCheck] at h0 h1 h2 h3 h4 h5 ⊢
    simp only [Linked.NatShr.program, List.all_append,
      h0, h1, h2, h3, h4, h5, Bool.and_self]
  intro row member
  have observed := List.all_eq_true.mp checked row member
  exact of_decide_eq_true observed

theorem original_entry :
    read_pc initial = BitVec.ofNat 64 Linked.NatShr.address ∧
    read_err initial = .None ∧ CheckSPAlignment initial ∧
    r (.GPR 1#5) initial = operand.pointer ∧
    r (.GPR 2#5) initial = operand.payload ∧
    r (.GPR 4#5) initial = 64#64 ∧ r (.GPR 5#5) initial = 0#64 := by
  decide

/-- The witness does not rely on unmapped storage, a zero Large pointer, wrapping
addresses, or an invalid allocator cursor. Empty spans are absent. -/
def writes : List Delimited.Span :=
  [(4096, 68), (32752, 16), (12304, 8), (20480, 256)]

theorem physical_regions :
    Codec.Storage.Physical 4096 68 8 ∧
    Codec.Storage.Physical 32752 16 16 ∧
    Codec.Storage.Physical 12288 24 8 ∧
    Codec.Storage.Physical 20480 256 8 ∧
    SszNative.Arena.Valid 20480 256 0 := by
  decide

theorem input_image :
    (Codec.Storage.Image.operand 8448 operand).Owned writes initial := by
  change 8448 + 16 ≤ 2^64 ∧ Delimited.Protected writes 8448 16 ∧
    Codec.Storage.Backing (Delimited.Protected writes) operand ∧
    SszNative.NatArithmetic.operandAt (UintCodec.widthLoad initial) 8448 operand
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp [Delimited.Protected, writes]
  · change 8 * 2 < 2^63 ∧ Delimited.Protected writes 8192 (8 * 2)
    constructor
    · decide
    · simp [Delimited.Protected, writes]
  · decide

/-- The source consumes the whole-limb offset and does not OR a second limb when
partial = 0. It returns Small 2 without consulting or changing the arena. -/
theorem source_result :
    SszNative.NatShift.shr operand 64 20480 256 0 =
      SszNative.NatArithmetic.unchanged 0 (.ok (.small 2#64)) := by
  rfl

/-- This is actual instruction execution starting at the original entry; neither
a continuation execution nor a helper result is supplied as a hypothesis. -/
def finalState : ArmState := run 84 initial

theorem machine_return :
    read_pc finalState = 16384#64 ∧ read_err finalState = .None ∧
    r (.GPR 31#5) finalState = 32768#64 := by
  decide

theorem machine_result :
    read_mem_bytes 8 4096#64 finalState = 0#64 ∧
    read_mem_bytes 8 4104#64 finalState = 7#64 ∧
    read_mem_bytes 4 4160#64 finalState = 0#32 ∧
    read_mem_bytes 8 12304#64 finalState = 0#64 := by
  decide

/-- Therefore the unrestricted source contract is false for this particular
linked image, even for a canonical two-limb operand and a valid u128 shift. -/
theorem not_source_result :
    ¬ SszNative.NatArithmetic.operandAt (UintCodec.widthLoad finalState)
      4096 (.small 2#64) := by
  intro result
  have payload := result.2.1
  change some (read_mem_bytes 8 4104#64 finalState).toNat = some 2 at payload
  rw [machine_result.2.1] at payload
  cases payload

end SszArm.Indices.NatShr.Counterexample
