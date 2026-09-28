import SszX86.MeasureBitsConstructorFinish

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- The actual CALL2114, linked Nat::from_u128 entry/RET, result discrimination,
and complete Plan/error publication. Ownership is derived from the prefix. -/
theorem constructor_body_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩)
    (headerReg : t.regs.rcx = s.regs.rcx)
    (outReg : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 24)
    (low : t.regs.rsi.toBitVec = (encodedWide bits.count).setWidth 64)
    (high : t.regs.rdx.toBitVec = ((encodedWide bits.count) >>> 64).setWidth 64) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc (.bits bits) buffer address capacity used u.1)
      (t, base + 2114) := by
  have range := count_call_used_range bits address capacity used
  have helperOwned := constructor_owned s t desc (.bits bits) buffer address capacity used
    (countUsed bits address capacity used) (base + 2119).toBitVec (encodedWide bits.count)
    owned resources.mapping resources.arena
    (by simpa only [count_used_nat] using range.1)
    (by simpa only [count_used_nat] using range.2)
    resources.stack headerReg outReg low high
  apply from_u128_call_cps e base hc
  · exact constructor_return_mapped s t desc (.bits bits) buffer address capacity used owned resources.mapping resources.stack
  apply eventually_trans (step e)
    (NatFromU128.Post (callState t (base + 2119).toBitVec) (encodedWide bits.count)
      address capacity (countUsed bits address capacity used) (base + 2119).toBitVec) _ _
  · simpa only [show Int64.ofNat NatFromU128.entry = 0 by decide, Int64.add_zero] using
      NatFromU128.from_u128_correct e (base + Int64.ofInt fromU128Offset) helpers.fromU128
        (callState t (base + 2119).toBitVec) (encodedWide bits.count) address capacity
        (countUsed bits address capacity used) (base + 2119).toBitVec helperOwned
  · rintro ⟨after, pc⟩ post
    have endpoint : pc = base + 2119 := by simpa using post.returned.pc
    subst pc
    exact constructor_finish_cps e base hc s after desc bits buffer address capacity used owned
      (constructor_resources s t (after, base + 2119) desc bits buffer address capacity used
        (base + 2119).toBitVec owned resources headerReg outReg helperOwned post) model

end SszX86.Measure.Bits
