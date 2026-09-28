import SszX86.NatMulMemoryBuffer
import SszX86.NatMulMemoryOutput
import SszX86.NatMulOutput
import SszX86.MemsetMemory
import SszX86.EmitMemcpyMemory

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- Convert the actual runtime memset byte postcondition to the initial limb
buffer. No preinitialized words or future loop observations are assumed. -/
theorem memset_zero_words (m : DataMem) (dst : BitVec 64) (count : Nat)
    (stored : Emit.ListBytesAt m dst (List.replicate (8*count) 0)) :
    NatMemory.wordsAt (widthLoad m) dst.toNat (List.replicate count 0) := by
  intro index
  have ix : index.val < count := by simpa only [List.length_replicate] using index.isLt
  have loaded := memmove_loadInt_of_lookup m (dst + BitVec.ofNat 64 (8*index.val))
    (List.replicate 8 (0 : UInt8)) (by
      intro j hj
      have byte : j < 8 := by simpa only [List.length_replicate] using hj
      have inside : 8*index.val+j < 8*count := by omega
      have lookup := stored (8*index.val+j) (by simpa only [List.length_replicate] using inside)
      rw [memmove_addr_add]
      simpa only [List.getElem?_replicate, ite_eq_left inside, ite_eq_left byte] using lookup)
  have zero : Mem.loadInt m (dst + BitVec.ofNat 64 (8*index.val)) 8 = some 0 := by
    simpa only [List.length_replicate, memset_replicate_ofBytes,
      show (0 : UInt8).toNat = 0 by rfl, Nat.zero_mul, Int.ofNat_eq_natCast, Int.ofNat_zero] using loaded
  unfold widthLoad
  rw [width_address, zero]
  simp

/-- The zero branch really writes payload before pointer; the accepted output
observation lemmas apply to these exact stores as well. -/
theorem zero_reads (m : DataMem) (out : BitVec 64) :
    NatArithmetic.AddResultAt (widthLoad (zeroMem m out)) out.toNat (.ok (.small 0)) := by
  change (widthLoad (zeroMem m out) out.toNat 8 = some 0 ∧
      widthLoad (zeroMem m out) (out.toNat+8) 8 = some 0 ∧ True) ∧
    widthLoad (zeroMem m out) (out.toNat+64) 4 = some 0
  refine ⟨⟨?_, ?_, trivial⟩, ?_⟩ <;> unfold zeroMem <;> natadd_result_reads

theorem zero_publish_frame (s : MachineData) (m : DataMem)
    (bound : s.regs.rdi.toNat+72 ≤ 2^64) :
    PublishFrame s m (zeroMem m s.regs.rdi.toBitVec) (.ok (.small 0)) := by
  intro a outside
  obtain ⟨pair, status⟩ := outside
  change s.regs.rdi.toBitVec.toNat+72 ≤ 2^64 at bound
  change Body.Outside a.toNat s.regs.rdi.toBitVec.toNat 16 at pair
  have statusFrame (before : DataMem) :
      (Mem.storeInt before (s.regs.rdi.toBitVec + BitVec.ofNat 64 64) 4 0).get? a =
        before.get? a := by
    apply memmove_store_lookup_outside
    intro i hi equal
    have byte : i < 4 := by simpa only [Int.toBytes_length] using hi
    change s.regs.rdi.toBitVec.toNat+72 ≤ 2^64 at bound
    change Body.Outside a.toNat (s.regs.rdi.toBitVec.toNat+64) 4 at status
    unfold Body.Outside at status
    bv_omega
  have pairFrame : ∀ i < 16, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
    intro i hi
    exact Body.outside_byte s.regs.rdi.toBitVec a 16 i (by omega) pair hi
  unfold zeroMem
  rw [statusFrame]
  simp (disch := first | exact pairFrame | decide) only [BoolCodec.store_frame (limit := 16)]

end SszX86.NatMul
