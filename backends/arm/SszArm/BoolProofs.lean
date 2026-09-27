import SszArm.BoolBody
import SszArm.BoolErrorMemory
import SszArm.BoolSuccessMemory
import SszArm.BoolFrames

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem body_result (s : ArmState) (base : BitVec 64) (hs : ScratchSeparated s) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (r (.GPR 0#5) s + BitVec.ofNat 64 offset) (bodyState s base)).toNat)
      (SszNative.BoolCodec.outcome (r (.GPR 3) s).toNat (UInt8.ofBitVec (inputByte s))) := by
  let l := lengthCompared s
  have hsl : ScratchSeparated l := by
    simpa (config := {decide := true})
      [ScratchSeparated, l, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules] using hs
  by_cases hn : r (.GPR 3) s = 1#64
  · let t := w .PC (base + 612#64) l
    let b := byteLoaded t
    have hsb : ScratchSeparated b := by
      simpa (config := {decide := true})
        [ScratchSeparated, b, t, byteLoaded, state_simp_rules] using hsl
    by_cases hz : inputByte s = 0#8
    · have hx : ScratchSeparated (w .PC (base + 4084#64) b) := by
        simpa [ScratchSeparated, state_simp_rules] using hsb
      simp only [bodyState, SszNative.BoolCodec.outcome, hn, hz, ↓reduceIte]
      simpa (config := {decide := true})
        [b, t, l, byteLoaded, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules]
        using success_tail_result (w .PC (base + 4084#64) b) base false hx
    · let c := byteCompared (w .PC (base + 620#64) b)
      have hsc : ScratchSeparated c := by
        simpa (config := {decide := true})
          [ScratchSeparated, c, byteCompared, state_simp_rules] using hsb
      have hz' : UInt8.ofBitVec (inputByte s) ≠ 0 := by
        intro h
        apply hz
        simpa using congrArg UInt8.toBitVec h
      by_cases ho : inputByte s = 1#8
      · have hx : ScratchSeparated (w .PC (base + 628#64) c) := by
          simpa [ScratchSeparated, state_simp_rules] using hsc
        simp only [bodyState, hn, hz, ↓reduceIte]
        simpa (config := {decide := true})
          [SszNative.BoolCodec.outcome, hn, ho, c, b, t, l, byteCompared, byteLoaded,
           lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules]
          using success_tail_result (w .PC (base + 628#64) c) base true hx
      · have hx : ScratchSeparated (w .PC (base + 4144#64) c) := by
          simpa [ScratchSeparated, state_simp_rules] using hsc
        have ho' : UInt8.ofBitVec (inputByte s) ≠ 1 := by
          intro h
          apply ho
          simpa using congrArg UInt8.toBitVec h
        have packed : (read_mem_bytes 1 (r (.GPR 2#5) s) s).toNat % 18446744073709551616 =
            (read_mem_bytes 1 (r (.GPR 2#5) s) s).toNat := by
          apply Nat.mod_eq_of_lt
          have h := (read_mem_bytes 1 (r (.GPR 2#5) s) s).isLt
          omega
        simp only [bodyState, SszNative.BoolCodec.outcome, hn, hz, ho, hz', ho', ↓reduceIte]
        simpa (config := {decide := true})
          [c, b, t, l,
           byteCompared, byteLoaded, lengthCompared, Udivti3.compare, Udivti3.next,
           state_simp_rules, inputByte, packed]
          using bad_tail_result (w .PC (base + 4144#64) c) base hx
  · have hn' : (r (.GPR 3) s).toNat ≠ 1 := by
      intro h
      apply hn
      apply BitVec.eq_of_toNat_eq
      simpa using h
    have hx : ScratchSeparated (w .PC (base + 2084#64) l) := by
      simpa [ScratchSeparated, state_simp_rules] using hsl
    simp only [bodyState, SszNative.BoolCodec.outcome, hn, hn', ↓reduceIte]
    simpa (config := {decide := true})
      [l, lengthCompared,
       Udivti3.compare, Udivti3.next, state_simp_rules]
      using scope_tail_result (w .PC (base + 2084#64) l) base hx

theorem body_upstream (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hs : ScratchSeparated s)
    (hlen : (r (.GPR 3) s).toNat = data.size)
    (hdata : data.size = 1 → inputByte s = data[0]!.toBitVec) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (r (.GPR 0#5) s + BitVec.ofNat 64 offset) (bodyState s base)).toNat)
      (Ssz.deserialize .bool data) := by
  apply SszNative.BoolCodec.result_refines
  have h := body_result s base hs
  by_cases hl : data.size = 1
  · have hb : UInt8.ofBitVec (inputByte s) = data[0]! := by
      simpa using congrArg UInt8.ofBitVec (hdata hl)
    simpa only [hlen, hb] using h
  · simpa only [hlen, SszNative.BoolCodec.outcome, if_neg hl] using h

/-- Postdispatch native Boolean decoding through RET, including output and memory framing. -/
theorem body_refines (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (hp : read_pc s = base + 604#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hs : ScratchSeparated s)
    (hout : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat + 272 ∨
      (r (.GPR 31#5) s).toNat + 368 ≤ (r (.GPR 0#5) s).toNat)
    (hlen : (r (.GPR 3) s).toNat = data.size)
    (hdata : data.size = 1 → inputByte s = data[0]!.toBitVec) :
    let final := run (bodySteps s) s
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (r (.GPR 0#5) s + BitVec.ofNat 64 offset) final).toNat)
      (Ssz.deserialize .bool data) ∧
    read_pc final = read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) s ∧
    r (.GPR 31#5) final = r (.GPR 31#5) s + 368#64 ∧
    (∀ reg offset, (reg, offset) ∈ savedRegisters →
      r (.GPR reg) final = read_mem_bytes 8
        (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s) ∧
    (∀ a : BitVec 64,
      (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 32 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
      final.mem a = s.mem a) := by
  dsimp only
  rw [body_run s base hc hp he ha]
  exact ⟨body_upstream s base data hs hlen hdata, body_return_pc s base hs hout,
    (body_exit s base).1, fun reg offset hr => body_register s base hs hout reg offset hr,
    fun a ha hb => body_frame s base a hs ha hb⟩

end SszArm.BoolCodec
