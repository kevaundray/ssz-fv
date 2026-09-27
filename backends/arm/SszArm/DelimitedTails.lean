import SszArm.DelimitedTailContracts
import SszDelimited

namespace SszArm.Delimited

open UintCodec (widthLoad)
open SszNative.Delimited (retainedBytes)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Both invalid-encoding exits start at the real common MOVI instruction. -/
theorem invalid_correct (entry s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 620#64) (saved : Saved entry s) (owned : TailOwned s)
    (reason : ((r (.GPR 9#5) s).setWidth 32 = 17#32) ∨
      ((r (.GPR 9#5) s).setWidth 32 = 18#32)) :
    ∃ t, run 25 s = t ∧ Returned entry t ∧ MemoryFrame (tailWrites s) s t ∧
      SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (.error (if (r (.GPR 9#5) s).setWidth 32 = 17#32 then
          .noDelimiter else .trailingZeros)) := by
  have exec := tail_run_returned .invalid entry s base hc he ha hp saved owned
  refine ⟨tailResult .invalid base s, exec.1, exec.2,
    tailMemoryFrame .invalid s base owned, ?_⟩
  have image := invalid_tail_image s base owned
  rcases reason with reason | reason <;>
    simpa [reason, SszNative.BitView.ResultAt] using image

/-- Allocation failure returns the exact native resource image after the
index-addressed output stores, saved-register reloads, and actual RET. -/
theorem scratch_correct (entry s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 752#64) (saved : Saved entry s) (owned : TailOwned s) :
    ∃ t, run 65 s = t ∧ Returned entry t ∧ MemoryFrame (tailWrites s) s t ∧
      SszNative.UintCodec.scratchExhaustedAt (widthLoad t) (r (.GPR 0#5) s).toNat := by
  have exec := tail_run_returned .scratch entry s base hc he ha hp saved owned
  exact ⟨tailResult .scratch base s, exec.1, exec.2,
    tailMemoryFrame .scratch s base owned, scratch_tail_image s base owned⟩

/-- The emitted code-2 result preserves arbitrary representable cap and actual
Nats, including immutable aliases and zero-length borrowed limb spans. -/
theorem over_limit_correct (entry s : ArmState) (base : BitVec 64) (expected actual : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 424#64) (saved : Saved entry s) (owned : TailOwned s)
    (expectedPair : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 22#5) s) (r (.GPR 21#5) s) expected)
    (actualPair : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 20#5) s) (r (.GPR 19#5) s) actual)
    (expectedOwned : NatOwned (tailWrites s) (r (.GPR 22#5) s) (r (.GPR 21#5) s))
    (actualOwned : NatOwned (tailWrites s) (r (.GPR 20#5) s) (r (.GPR 19#5) s)) :
    ∃ t, run 53 s = t ∧ Returned entry t ∧ MemoryFrame (tailWrites s) s t ∧
      SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (.error (.overLimit expected actual)) := by
  have exec := tail_run_returned .overLimit entry s base hc he ha hp saved owned
  exact ⟨tailResult .overLimit base s, exec.1, exec.2,
    tailMemoryFrame .overLimit s base owned,
    over_limit_tail_image s base expected actual owned expectedPair actualPair
      expectedOwned actualOwned⟩

/-- Exactly the branch path selected by the delimiter's low-three-bit index.
Neither overflowOps nor the p684 BadRepresentation block occurs on this path. -/
def representationOps (highest : Nat) : List Op :=
  representationTestOps ++ (if highest = 0 then alignedByteOps else unalignedByteOps) ++
    representationSumOps ++ noOverflowOps ++ representationJoinOps

def representationState (base : BitVec 64) (highest : Nat) (s : ArmState) : ArmState :=
  block base (representationOps highest) s

private theorem cmp32_zero (a b : BitVec 32) :
    (AddWithCarry a (~~~b) 1#1).2.z = 1#1 ↔ a = b := by
  change (if (AddWithCarry a (~~~b) 1#1).1 = 0#32 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_sub_neg]
  simp only [BitVec.not_not]
  have hz : a - b = 0#32 ↔ a = b := by bv_omega
  simpa using hz

private theorem representation_zero (highest : Nat) (bit : highest < 8) :
    (AddWithCarry (BitVec.ofNat 32 (7 - highest)) 4294967288#32 1#1).2.z = 1#1 ↔
      highest = 0 := by
  change (AddWithCarry (BitVec.ofNat 32 (7 - highest)) (~~~7#32) 1#1).2.z = 1#1 ↔ _
  rw [cmp32_zero]
  bv_omega

private theorem representation_no_carry (length highest : Nat)
    (nonempty : 0 < length) (physical : length < 2^64) :
    (AddWithCarry (if highest = 0 then 0#64 else 1#64)
      (BitVec.ofNat 64 (length - 1)) 0#1).2.c ≠ 1#1 := by
  intro overflow
  have carry := (Udivti3.adc_carry _ _ _).mp overflow
  have prefixBound : length - 1 < 2^64 := by omega
  by_cases hz : highest = 0 <;>
    simp only [hz, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt prefixBound,
      Udivti3.radix] at carry <;> omega

private theorem representation_sum (length highest : Nat)
    (nonempty : 0 < length) (physical : length < 2^64) :
    (if highest = 0 then 0#64 else 1#64) + BitVec.ofNat 64 (length - 1) =
      BitVec.ofNat 64 (retainedBytes length highest) := by
  unfold retainedBytes
  split <;> bv_omega

/-- Physical unsigned length is sufficient: there is no isize/2^63 premise.
This proves both conditional branches and the actual XOR/OR join to be safe. -/
theorem representation_run (s : ArmState) (base : BitVec 64) (length highest : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 540#64)
    (nonempty : 0 < length) (physical : length < 2^64) (bit : highest < 8)
    (lenReg : r (.GPR 3#5) s = BitVec.ofNat 64 length)
    (prefixReg : r (.GPR 25#5) s = BitVec.ofNat 64 (length - 1))
    (clzReg : (r (.GPR 26#5) s).setWidth 32 = BitVec.ofNat 32 (7 - highest)) :
    run (representationOps highest).length s = representationState base highest s := by
  apply block_run base (representationOps highest) s hc he ha
  have hpc : r .PC s = base + 540#64 := hp
  have zero := representation_zero highest bit
  have carry := representation_no_carry length highest nonempty physical
  have sum := representation_sum length highest nonempty physical
  by_cases hz : highest = 0 <;>
    simp only [hz, ↓reduceIte, retainedBytes] at carry sum
  all_goals
    simp (config := {decide := true, instances := true})
      [representationOps, representationTestOps, alignedByteOps, unalignedByteOps,
       representationSumOps, noOverflowOps, representationJoinOps, Follows, Op.row,
       Op.effect, put, next, state_simp_rules, hpc, lenReg, prefixReg, clzReg,
       zero, hz, carry, sum, BitVec.add_assoc]

/-- The exact post-check values explain why the p592 CBNZ cannot reach p684. -/
theorem representation_values (s : ArmState) (base : BitVec 64) (length highest : Nat)
    (nonempty : 0 < length) (physical : length < 2^64) (bit : highest < 8)
    (lenReg : r (.GPR 3#5) s = BitVec.ofNat 64 length)
    (prefixReg : r (.GPR 25#5) s = BitVec.ofNat 64 (length - 1))
    (clzReg : (r (.GPR 26#5) s).setWidth 32 = BitVec.ofNat 32 (7 - highest)) :
    read_pc (representationState base highest s) = base + 596#64 ∧
      r (.GPR 8#5) (representationState base highest s) = 0#64 ∧
      r (.GPR 9#5) (representationState base highest s) =
        BitVec.ofNat 64 (retainedBytes length highest) := by
  have zero := representation_zero highest bit
  have sum := representation_sum length highest nonempty physical
  by_cases hz : highest = 0 <;>
    simp only [hz, ↓reduceIte, retainedBytes] at sum
  all_goals
    simp only [hz, Nat.sub_zero] at zero
    simp [representationState, representationOps, representationTestOps,
      alignedByteOps, unalignedByteOps, representationSumOps, noOverflowOps,
      representationJoinOps, block, Op.effect, put, next, state_simp_rules,
      lenReg, prefixReg, clzReg, zero, hz, sum, retainedBytes]

/-- All non-temporary registers, memory, and SIMD lanes survive the check. -/
theorem representation_register (s : ArmState) (base : BitVec 64) (highest : Nat)
    (reg : BitVec 5) (ne8 : reg ≠ 8#5) (ne9 : reg ≠ 9#5) (ne10 : reg ≠ 10#5) :
    r (.GPR reg) (representationState base highest s) = r (.GPR reg) s := by
  by_cases hz : highest = 0 <;>
    simp [representationState, representationOps, representationTestOps,
      alignedByteOps, unalignedByteOps, representationSumOps, noOverflowOps,
      representationJoinOps, block, Op.effect, put, next, state_simp_rules,
      hz, ne8, ne9, ne10]

theorem representation_memory (s : ArmState) (base : BitVec 64) (highest : Nat) :
    (representationState base highest s).mem = s.mem := by
  by_cases hz : highest = 0 <;>
    simp [representationState, representationOps, representationTestOps,
      alignedByteOps, unalignedByteOps, representationSumOps, noOverflowOps,
      representationJoinOps, block, Op.effect, put, next, state_simp_rules, hz]

theorem representation_load (s : ArmState) (base : BitVec 64) (highest : Nat) :
    widthLoad (representationState base highest s) = widthLoad s := by
  funext a n
  unfold widthLoad
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (representation_memory s base highest)) n]

theorem representation_vectors (s : ArmState) (base : BitVec 64) (highest : Nat)
    (reg : BitVec 5) :
    r (.SFP reg) (representationState base highest s) = r (.SFP reg) s := by
  by_cases hz : highest = 0 <;>
    simp [representationState, representationOps, representationTestOps,
      alignedByteOps, unalignedByteOps, representationSumOps, noOverflowOps,
      representationJoinOps, block, Op.effect, put, next, state_simp_rules, hz]

/-- Successful decode from the real representation-check start through RET.
The borrowed byte count, full count limbs, and impossibility of reason 32770
are derived from the physical length and delimiter-bit arithmetic. -/
theorem success_correct (entry s : ArmState) (base : BitVec 64)
    (length highest : Nat) (packed : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 540#64) (saved : Saved entry s) (owned : TailOwned s)
    (nonempty : 0 < length) (physical : length < 2^64) (bit : highest < 8)
    (lenReg : r (.GPR 3#5) s = BitVec.ofNat 64 length)
    (prefixReg : r (.GPR 25#5) s = BitVec.ofNat 64 (length - 1))
    (clzReg : (r (.GPR 26#5) s).setWidth 32 = BitVec.ofNat 32 (7 - highest))
    (countLow : r (.GPR 24#5) s = BitVec.ofNat 64 (8 * (length - 1) + highest))
    (countHigh : r (.GPR 23#5) s =
      BitVec.ofNat 64 ((8 * (length - 1) + highest) / 2^64))
    (packedSize : packed.size = retainedBytes length highest)
    (dataPhysical : (r (.GPR 2#5) s).toNat + packed.size ≤ 2^64)
    (dataOwned : Protected (tailWrites s) (r (.GPR 2#5) s).toNat packed.size)
    (input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat packed) :
    ∃ t, run ((representationOps highest).length + 13) s = t ∧
      Returned entry t ∧ MemoryFrame (tailWrites s) s t ∧
      SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (.ok (.bits (Ssz.unpackBits packed (8 * (length - 1) + highest)))) := by
  let u := representationState base highest s
  have registers := representation_register s base highest
  have out : r (.GPR 0#5) u = r (.GPR 0#5) s := registers _ (by decide) (by decide) (by decide)
  have sp : r (.GPR 31#5) u = r (.GPR 31#5) s := registers _ (by decide) (by decide) (by decide)
  have ptr : r (.GPR 2#5) u = r (.GPR 2#5) s := registers _ (by decide) (by decide) (by decide)
  have low : r (.GPR 24#5) u = BitVec.ofNat 64 (8 * (length - 1) + highest) :=
    (registers _ (by decide) (by decide) (by decide)).trans countLow
  have high : r (.GPR 23#5) u = BitVec.ofNat 64 ((8 * (length - 1) + highest) / 2^64) :=
    (registers _ (by decide) (by decide) (by decide)).trans countHigh
  have writes : tailWrites u = tailWrites s := by simp only [tailWrites, out, sp]
  have memory : MemoryFrame (tailWrites s) s u := by
    intro a _
    exact congrFun (representation_memory s base highest) a
  have ownership : TailOwned u := by
    constructor
    · simpa only [sp] using owned.stackLow
    · simpa only [sp] using owned.stackHigh
    · simpa only [out] using owned.output
    · simpa only [out, sp] using owned.working
    · simpa only [out, sp] using owned.activation
  have saved' : Saved entry u := saved.frame memory sp owned.stackHigh
    owned.activation_protected (by
      intro reg lo hi
      rw [show r (.SFP reg) u = r (.SFP reg) s from representation_vectors s base highest reg])
  have code : CodeAt u base := by
    simpa only [u, representationState, CodeAt, block_program] using hc
  have err : read_err u = .None := by
    simpa only [u, representationState, block_error] using he
  have align : CheckSPAlignment u := block_aligned base (representationOps highest) s ha
  have values := representation_values s base length highest nonempty physical bit lenReg prefixReg clzReg
  have exec := tail_run_returned .success entry u base code err align values.1 saved' ownership
  have arithmetic := representation_check length highest nonempty physical bit
  have scope : packed.size = (8 * (length - 1) + highest + 7) / 8 :=
    packedSize.trans arithmetic.2.2
  have byteBound : packed.size < 2^64 := by
    rw [packedSize]
    unfold retainedBytes
    split <;> omega
  have countBound : 8 * (length - 1) + highest < 2^128 := by omega
  have image := success_tail_image u base packed (8 * (length - 1) + highest)
    ownership (by simpa only [ptr] using dataPhysical) byteBound countBound scope
    (by simpa only [packedSize] using values.2.2) low high values.2.1
    (by simpa only [writes, ptr] using dataOwned)
    (by simpa only [u, representation_load, ptr] using input)
  refine ⟨tailResult .success base u, ?_, exec.2, ?_, ?_⟩
  · rw [run_plus, representation_run s base length highest hc he ha hp
      nonempty physical bit lenReg prefixReg clzReg]
    exact exec.1
  · exact memory.trans (by simpa only [writes] using tailMemoryFrame .success u base ownership)
  · simpa only [out] using image

end SszArm.Delimited
