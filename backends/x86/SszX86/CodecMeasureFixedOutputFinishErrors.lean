import SszX86.CodecMeasureFixedOutputFinishPost
import SszX86.CodecMeasureFixedOutputErrorImage
import SszX86.CodecMeasureFixedOutputCopy344
import SszX86.CodecMeasureFixedOutputCopy455
import SszX86.CodecMeasureFixedOutputCopy607
import SszX86.CodecMeasureFixedOutputCopy709

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec Serialize.Publish

/-- Each error finish is a finite actual copy followed by the actual epilogue.
The current scratch image fixes only active fields, never its opaque padding. -/
theorem finish_error344 {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (reason : NatArithmetic.Failure) (v : Image)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result =
      .error (.arithmetic reason))
    (image : ImageAt body.dmem body.regs.rsp.toBitVec v)
    (active : ArithmeticErrorImage reason v)
    (apart : Large.Disjoint body.regs.rsp.toBitVec body.regs.rbx.toBitVec 72 72)
    (r14 : body.regs.r14.toBitVec = v.w0) (r15 : body.regs.r15.toBitVec = v.w1)
    (rcx : body.regs.rcx.toBitVec = v.w2)
    (rax : body.regs.rax.toBitVec = v.tag.setWidth 64) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 344) := by
  apply copy344_cps e base code body v image apart pending.mapped r14 r15 rcx rax
  apply finish_published e code owned pending (copied344 body v) rfl rfl
  · simpa only [copied344, result, pending.output] using
      copy344_frame body.dmem body.regs.rbx.toBitVec v (.arithmetic reason)
  · have bound : body.regs.rbx.toBitVec.toNat + 72 ≤ 2^64 := by
      simpa only [pending.output] using owned.output_bound
    have observed := arithmetic_image_observed _ body.regs.rbx.toBitVec v reason
      (copy344_image body.dmem body.regs.rbx.toBitVec v bound) active
    simpa only [copied344, result, pending.output, UInt64.toNat_toBitVec] using observed

theorem finish_error455 {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (reason : NatArithmetic.Failure) (v : Image)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result =
      .error (.arithmetic reason))
    (image : ImageAt body.dmem body.regs.rsp.toBitVec v)
    (active : ArithmeticErrorImage reason v)
    (apart : Large.Disjoint body.regs.rsp.toBitVec body.regs.rbx.toBitVec 72 72)
    (rcx : body.regs.rcx.toBitVec = v.w0) (rsi : body.regs.rsi.toBitVec = v.w1)
    (rdx : body.regs.rdx.toBitVec = v.w2)
    (rax : body.regs.rax.toBitVec = v.tag.setWidth 64) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 455) := by
  apply copy455_cps e base code body v image apart pending.mapped rcx rsi rdx rax
  apply finish_published e code owned pending (copied455 body v) rfl rfl
  · simpa only [copied455, result, pending.output] using
      copy455_frame body.dmem body.regs.rbx.toBitVec v (.arithmetic reason)
  · have bound : body.regs.rbx.toBitVec.toNat + 72 ≤ 2^64 := by
      simpa only [pending.output] using owned.output_bound
    have observed := arithmetic_image_observed _ body.regs.rbx.toBitVec v reason
      (copy455_image body.dmem body.regs.rbx.toBitVec v bound) active
    simpa only [copied455, result, pending.output, UInt64.toNat_toBitVec] using observed

theorem finish_error607 {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (reason : NatArithmetic.Failure) (v : Image)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result =
      .error (.arithmetic reason))
    (image : ImageAt body.dmem body.regs.rsp.toBitVec v)
    (active : ArithmeticErrorImage reason v)
    (apart : Large.Disjoint body.regs.rsp.toBitVec body.regs.rbx.toBitVec 72 72)
    (r14 : body.regs.r14.toBitVec = v.w0) (r15 : body.regs.r15.toBitVec = v.w1)
    (rax : body.regs.rax.toBitVec = v.tag.setWidth 64) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 607) := by
  apply copy607_cps e base code body v image apart pending.mapped r14 r15 rax
  apply finish_published e code owned pending (copied607 body v) rfl rfl
  · simpa only [copied607, result, pending.output] using
      copy607_frame body.dmem body.regs.rbx.toBitVec v (.arithmetic reason)
  · have bound : body.regs.rbx.toBitVec.toNat + 72 ≤ 2^64 := by
      simpa only [pending.output] using owned.output_bound
    have observed := arithmetic_image_observed _ body.regs.rbx.toBitVec v reason
      (copy607_image body.dmem body.regs.rbx.toBitVec v bound) active
    simpa only [copied607, result, pending.output, UInt64.toNat_toBitVec] using observed

theorem finish_error709 {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (reason : NatArithmetic.Failure) (v : Image)
    (result : (FixedSize.measureFixed desc (arenaState address capacity used)).result =
      .error (.arithmetic reason))
    (image : ImageAt body.dmem body.regs.rsp.toBitVec v)
    (active : ArithmeticErrorImage reason v)
    (apart : Large.Disjoint body.regs.rsp.toBitVec body.regs.rbx.toBitVec 72 72)
    (rdx : body.regs.rdx.toBitVec = v.w0) (rcx : body.regs.rcx.toBitVec = v.w1)
    (r8 : body.regs.r8.toBitVec = v.w2)
    (rax : body.regs.rax.toBitVec = v.tag.setWidth 64) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (body, base + 709) := by
  apply copy709_cps e base code body v image apart pending.mapped rdx rcx r8 rax
  apply finish_published e code owned pending (copied709 body v) rfl rfl
  · simpa only [copied709, result, pending.output] using
      copy455_frame body.dmem body.regs.rbx.toBitVec v (.arithmetic reason)
  · have bound : body.regs.rbx.toBitVec.toNat + 72 ≤ 2^64 := by
      simpa only [pending.output] using owned.output_bound
    have observed := arithmetic_image_observed _ body.regs.rbx.toBitVec v reason
      (copy455_image body.dmem body.regs.rbx.toBitVec v bound) active
    simpa only [copied709, result, pending.output, UInt64.toNat_toBitVec] using observed

end SszX86.CodecMeasureFixed.Output
