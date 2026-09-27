import SszX86.MemcpyProofs
import SszBytes

namespace SszX86

/-- The validated byte-vector/list payload copy returns the exact upstream
encoding in caller-owned memory. Reading those output bytes with the upstream
decoder recovers the original value. This composes the actual memcpy execution,
including RET and its complete frame; it does not prove native descriptor
validation, dispatch, or decoder execution. -/
theorem memcpy_ssz (base : Int64) (s : MachineData) (desc : Ssz.Desc)
    (xs old : List UInt8) (frame : DataMem) (ra : BitVec 64)
    (hfits : Ssz.Value.fits desc (.bytes xs.toArray) = true)
    (hlen : old.length = xs.length)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length)
    (hb : xs.length < 2^64)
    (hmem : CopyMem s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old (Eq frame))
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hsep : ∀ i < 8, ∀ j < xs.length,
      s.regs.rsp.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rdi.toBitVec + BitVec.ofNat 64 j) :
    Eventually (memcpyStep base) (fun st =>
      MemcpyReturned s ra st ∧
      CopyMem st.1.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs xs (Eq frame) ∧
      (∀ a, a ∉ xs.At s.regs.rdi.toBitVec → st.1.dmem.get? a = s.dmem.get? a) ∧
      ∃ encoded : Ssz.Bytes,
        (Mem.loadBytes st.1.dmem s.regs.rdi.toBitVec xs.length).map List.toArray =
          some encoded ∧
        Ssz.serialize desc (.bytes xs.toArray) = .ok encoded ∧
        Ssz.deserialize desc encoded = .ok (.bytes xs.toArray)) (s, base) := by
  have run := memcpy_correct base s xs old frame ra hlen hcount hb hmem hr hsep
  apply eventually_weaken _ _ _ _ ?_ run
  rintro st ⟨hret, hcopy, hframe⟩
  refine ⟨hret, hcopy, hframe, xs.toArray, ?_, SszNative.bytes_codec desc _ hfits⟩
  have load := Mem.loadBytes_sep xs s.regs.rdi.toBitVec xs.length
    (Eq (xs.At s.regs.rsi.toBitVec) ⋆ Eq frame) st.1.dmem hcopy rfl (by omega)
  rw [load]
  rfl

end SszX86
