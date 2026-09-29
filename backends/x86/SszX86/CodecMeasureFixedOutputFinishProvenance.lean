import SszX86.CodecMeasureFixedOutputFinishSuccess
import SszX86.CodecMeasureFixedProvenance
import SszX86.CodecMeasureFixedArithmeticOwnershipMemory

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec

/-- Borrowed-width separation is derived from the original readonly graph and
actual allocation provenance, never postulated for a future helper result. -/
theorem width_output_apart {original : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    (width : NatOperand)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result = .ok (some width))
    (current : DataMem) (borrowed : width.At (widthLoad current)) :
    ∀ p words, width = .large p words →
      Body.Apart p.toNat (8*words.length) original.regs.rdi.toNat 68 := by
  intro p words equality
  subst width
  have bound := borrowed.2.2.1
  apply arithmetic_apart_of_disjoint _ _ _ _ bound (by have := owned.output_bound; omega)
  intro a inside output
  simp only [BitVec.ofNat_toNat] at inside output
  have output72 : Codec.InSpan a original.regs.rdi.toBitVec 72 := by
    rcases output with ⟨i, hi, equal⟩
    exact ⟨i, by omega, equal⟩
  have provenance := measure_fixed_provenance original.dmem r original.regs.rsi.toBitVec
    desc owned.descriptor (arenaState address capacity used) (.large p words) result a inside
  rcases provenance with readonly | allocation
  · exact owned.readonly a readonly (Or.inl output72)
  · have geometry := measureFixed_trace_geometry desc (arenaState address capacity used)
      owned.arena_bound owned.used_bound
    have location := geometry.writes a allocation
    have upper := geometry.upper
    change address.toNat + used.toNat ≤ a.toNat ∧
      a.toNat < address.toNat + (FixedSize.measureFixed desc (arenaState address capacity used)).used
      at location
    change (FixedSize.measureFixed desc (arenaState address capacity used)).used ≤ capacity.toNat at upper
    have outPosition := span_bounds owned.output_bound output72
    have apart := owned.arena_output.nonempty (by omega) (by decide)
    omega

/-- Root-ready Some finish; the only width premise is its current physical image. -/
theorem finish_some_owned {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (width : NatOperand)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result = .ok (some width))
    (pointer : body.regs.r14.toBitVec = width.pointer)
    (payload : body.regs.r15.toBitVec = width.payload)
    (borrowed : width.At (widthLoad body.dmem)) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 271) :=
  finish_some e code owned pending width result pointer payload borrowed
    (width_output_apart owned width result body.dmem borrowed)

end SszX86.CodecMeasureFixed.Output
