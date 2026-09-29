import SszArm.CodecEmitUnionRound
import SszArm.CodecStorageLegacy

namespace SszArm.Codec.Emit.Union.Scan

open SszNative (NatOperand)
open SszNative.Codec (Desc)
open UintCodec (widthLoad)
open Delimited (Protected)

def scanWrites (s : ArmState) : List Delimited.Span :=
  Stack.envelope (r (.GPR 31#5) s).toNat 16

/-- Original read-only observations at one remaining variant-slice boundary. -/
structure Ready (s : ArmState) (address : Nat) (variants : List (NatOperand × Desc))
    (selector : NatOperand) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  bound : address + 24 * variants.length ≤ 2 ^ 64
  cursor : r (.GPR 26#5) s = BitVec.ofNat 64 address - 24#64
  count : r (.GPR 27#5) s = BitVec.ofNat 64 (24 * variants.length)
  pointer : r (.GPR 23#5) s = selector.pointer
  payload : r (.GPR 24#5) s = selector.payload
  selector : selector.At (widthLoad s)
  selectorOwned : NatDivision.OperandOwned (scanWrites s) selector
  variants : (Storage.variantEntries address variants).Owned (scanWrites s) s

/-- An exact borrowed operand is protected against Nat.compare's real lowering
slot even when Large carries no limbs or carries redundant high zero limbs. -/
theorem operand_compare_owned (s : ArmState) (operand : NatOperand)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat) (physical : operand.At (widthLoad s))
    (owned : NatDivision.OperandOwned (scanWrites s) operand) :
    NatCompare.Owned s operand.pointer operand.payload := by
  refine ⟨low, ?_⟩
  cases operand with
  | small word => simp [NatOperand.pointer]
  | large pointer words =>
    intro nonzero nonempty
    have countBound : words.length < 2 ^ 64 := by have := physical.2.2.1; omega
    have count : (NatOperand.large pointer words).payload.toNat = words.length := by
      simp only [NatOperand.payload, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
    rw [count]
    change Protected (scanWrites s) pointer.toNat (8 * words.length) at owned
    rcases owned with empty | apart
    · have zero : words.length = 0 := by omega
      exact False.elim (nonempty (by simp [NatOperand.payload, zero]))
    · have separate := apart ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [scanWrites, Stack.envelope])
      simp only [NatOperand.pointer, Prod.fst, Prod.snd] at separate ⊢
      omega

theorem ready_nonempty (s : ArmState) (address : Nat) (key : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (selector : NatOperand)
    (ready : Ready s address ((key, desc) :: rest) selector) : r (.GPR 27#5) s ≠ 0#64 := by
  have positive : 0 < address := ready.variants.1.1.1.1
  have countBound : 24 * ((key, desc) :: rest).length < 2 ^ 64 := by
    have := ready.bound
    omega
  rw [ready.count]
  intro zero
  have numeric := congrArg BitVec.toNat zero
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at numeric
  simp at numeric

theorem head_header (s : ArmState) (address : Nat) (key : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (selector : NatOperand)
    (ready : Ready s address ((key, desc) :: rest) selector) :
    read_mem_bytes 8 (r (.GPR 26#5) s + 32#64) s = key.pointer ∧
      read_mem_bytes 8 (r (.GPR 26#5) s + 40#64) s = key.payload := by
  have header := ready.variants.1.2.1.2.2.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    have observed := Option.some.inj header.1
    simpa only [widthLoad, ready.cursor, BitVec.ofNat_add, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      show -24#64 + 32#64 = 8#64 by decide] using observed
  · apply BitVec.eq_of_toNat_eq
    have observed := Option.some.inj header.2.1
    simpa only [widthLoad, ready.cursor, BitVec.ofNat_add, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      show -24#64 + 40#64 = 16#64 by decide,
      show 8#64 + 8#64 = 16#64 by decide] using observed

theorem ready_round (s : ArmState) (bias : BitVec 64) (address : Nat)
    (key : NatOperand) (desc : Desc) (rest : List (NatOperand × Desc)) (selector : NatOperand)
    (ready : Ready s address ((key, desc) :: rest) selector)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = bias + 2296416#64) :
    ∃ fuel t, run fuel s = t ∧ Round s t bias key.value selector.value := by
  have header := head_header s address key desc rest selector ready
  have operand := ready.variants.1.2.1
  have stored := operand.2.2.2
  apply round_correct s bias key.value selector.value code error aligned pc
    (ready_nonempty s address key desc rest selector ready)
  · rw [header.1, header.2]
    exact NatOperand.At.pair (widthLoad s) key stored.2.2
  · rw [ready.pointer, ready.payload]
    exact NatOperand.At.pair (widthLoad s) selector ready.selector
  · rw [header.1, header.2]
    exact operand_compare_owned s key ready.stackLow stored.2.2 (Storage.operand_owned operand)
  · rw [ready.pointer, ready.payload]
    exact operand_compare_owned s selector ready.stackLow ready.selector ready.selectorOwned

/-- A completed nonmatching round consumes exactly one physical Variant and
keeps the remaining borrowed array, including every aliased descriptor node. -/
theorem ready_tail {s t : ArmState} {bias : BitVec 64} {address : Nat}
    {key : NatOperand} {desc : Desc} {rest : List (NatOperand × Desc)} {selector : NatOperand}
    (ready : Ready s address ((key, desc) :: rest) selector)
    (round : Round s t bias key.value selector.value) :
    Ready t (address + 24) rest selector := by
  have frame : Delimited.MemoryFrame (scanWrites s) s t := round.frame
  have keyPointer := round.preserved 23#5 (by decide)
  have keyPayload := round.preserved 24#5 (by decide)
  have storage := Storage.Image.preserved (Storage.variantEntries address ((key, desc) :: rest))
    frame ready.variants
  have source : selector.At (widthLoad t) := by
    cases selector with
    | small word => trivial
    | large pointer words =>
      refine ⟨ready.selector.1, ready.selector.2.1, ready.selector.2.2.1, ?_⟩
      intro index
      have physical := ready.selector.2.2.1
      have count := index.isLt
      rw [frame.load (pointer.toNat + 8 * index.val) 8 (by omega)
        (ready.selectorOwned.subspan (8 * index.val) 8 (by omega))]
      exact ready.selector.2.2.2 index
  refine ⟨by simpa only [round.stack] using ready.stackLow,
    by have := ready.bound; simp only [List.length_cons] at this; omega,
    ?_, ?_, keyPointer.trans ready.pointer, keyPayload.trans ready.payload,
    source, ?_, ?_⟩
  · rw [round.cursor, ready.cursor, BitVec.ofNat_add]
    simp only [BitVec.sub_add_cancel, BitVec.add_sub_cancel]
  · rw [round.remaining, ready.count]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  · simpa only [scanWrites, round.stack] using ready.selectorOwned
  · simpa only [scanWrites, round.stack] using storage.2

end SszArm.Codec.Emit.Union.Scan
