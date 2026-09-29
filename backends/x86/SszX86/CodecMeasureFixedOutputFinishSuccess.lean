import SszX86.CodecMeasureFixedOutputFinishPost
import SszX86.CodecMeasureFixedOutputFacts

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec

/-- Complete the real None publication and restoring return, from its current cut. -/
theorem finish_none {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result = .ok none) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 680) := by
  apply none_cps e base code body pending.mapped
  apply finish_published e code owned pending (publishedNone body) rfl rfl
  · simpa only [publishedNone, pending.output, result] using none_frame body
  · have bound : body.regs.rbx.toNat + 72 ≤ 2^64 := by
      simpa only [← UInt64.toNat_toBitVec, pending.output] using owned.output_bound
    simpa only [publishedNone, result, ← UInt64.toNat_toBitVec, pending.output]
      using none_observed body bound

/-- Complete Some publication from the actual width pair and borrowed limb image.
The disjointness is a current physical ownership condition, not future execution. -/
theorem finish_some {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (width : NatOperand)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result = .ok (some width))
    (pointer : body.regs.r14.toBitVec = width.pointer)
    (payload : body.regs.r15.toBitVec = width.payload)
    (borrowed : width.At (widthLoad body.dmem))
    (apart : ∀ p words, width = .large p words →
      Body.Apart p.toNat (8*words.length) original.regs.rdi.toNat 68) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 271) := by
  apply some_cps e base code body pending.mapped
  apply finish_published e code owned pending (publishedSome body) rfl rfl
  · simpa only [publishedSome, pending.output, result] using some_frame body width
  · have bound : body.regs.rbx.toNat + 72 ≤ 2^64 := by
      simpa only [← UInt64.toNat_toBitVec, pending.output] using owned.output_bound
    have separate : ∀ p words, width = .large p words →
        Body.Apart p.toNat (8*words.length) body.regs.rbx.toNat 68 := by
      simpa only [← UInt64.toNat_toBitVec, pending.output] using apart
    simpa only [publishedSome, result, ← UInt64.toNat_toBitVec, pending.output]
      using some_observed body width bound pointer payload borrowed separate

end SszX86.CodecMeasureFixed.Output
