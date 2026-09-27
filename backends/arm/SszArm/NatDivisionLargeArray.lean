import SszArm.NatDivisionLargeMemory
import SszArm.NatDivisionScanNormalize
import SszArm.NatDivisionClassify

namespace SszArm.NatDivision

open Delimited (MemoryFrame)
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The registers needed after copy, reverse division, and normalization. -/
structure LargeArrayFrame (destination : BitVec 64) (count : Nat) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∈ [19#5, 20#5, 25#5, 26#5, 27#5, 28#5, 29#5, 31#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : MemoryFrame (loopWrites (r (.GPR 31#5) s) destination count) s t

/-- Real copy, actual runtime-backed reverse division, and full normalization
compose over arbitrary physical input lists. The original high zeros are not
reinterpreted as canonical input, and every quotient position remains observable. -/
theorem large_array_run (s : ArmState) (base pointer destination divisor : BitVec 64)
    (words : List (BitVec 64))
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 452#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words))
    (h9 : r (.GPR 9#5) s = 0#64)
    (h20 : r (.GPR 20#5) s = divisor)
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (sigWords words + 1))
    (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * (sigWords words - 1)))
    (h24 : r (.GPR 24#5) s = destination)
    (positive : 0 < sigWords words) (domain : 2 ≤ divisor.toNat)
    (source : NatCompare.Source s pointer words) (input : NatCompare.Words s pointer words)
    (storage : CopyDestination s destination (sigWords words))
    (apart : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * sigWords words ≤ pointer.toNat) :
    ∃ fuel t, run fuel s = t ∧ LargeArrayFrame destination (sigWords words) s t ∧
      read_pc t = base + 1120#64 ∧ r (.GPR 8#5) t = 0#64 ∧
      r (.GPR 24#5) t = (SszNative.NatOperand.fromWords destination
        (SszNative.LimbDivision.divideWords divisor (trim words)).1).pointer ∧
      r (.GPR 10#5) t = (SszNative.NatOperand.fromWords destination
        (SszNative.LimbDivision.divideWords divisor (trim words)).1).payload ∧
      (r (.GPR 1#5) t).toNat = (SszNative.LimbDivision.divideWords divisor (trim words)).2 ∧
      NatCompare.Words t destination (SszNative.LimbDivision.divideWords divisor (trim words)).1 := by
  obtain ⟨copyFuel, u, copyRun, copyFrame, copyPC, copyPointer, copyIndex, copied, _, _⟩ :=
    copy_significant s base pointer destination words hc.1 he ha hp h1 h2 h8 h9 h24 positive source input storage apart
  have uc : JointCodeAt u base := by
    simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, copyFrame.program] using hc
  have u24 : r (.GPR 24#5) u = destination := (copyFrame.registers 24#5 (by decide)).trans h24
  have u20 : r (.GPR 20#5) u = divisor := (copyFrame.registers 20#5 (by decide)).trans h20
  have u22 : r (.GPR 22#5) u = BitVec.ofNat 64 ((trim words).length + 1) := by
    simpa only [trim_length] using (copyFrame.registers 22#5 (by decide)).trans h22
  have u23 : r (.GPR 23#5) u = BitVec.ofNat 64 (8 * ((trim words).length - 1)) := by
    simpa only [trim_length] using (copyFrame.registers 23#5 (by decide)).trans h23
  have us : LoopSpace (r (.GPR 31#5) u) (r (.GPR 24#5) u) (trim words).length := by
    rw [copyFrame.sp, u24, trim_length]
    exact ⟨source.1, storage.1, storage.2⟩
  have um : LoopWords u (r (.GPR 24#5) u) (trim words) := by
    rw [u24]
    exact loopWords_of_words u destination (trim words) copied
  have nonempty : trim words ≠ [] := by
    intro empty
    have length := trim_length words
    rw [empty] at length
    simp only [List.length_nil] at length
    omega
  obtain ⟨loopFuel, v, loopRun, loopFrame, divided, remainder, _, loopPC⟩ :=
    divideWords_run (trim words) u base divisor nonempty uc (copyFrame.error.trans he)
      (copyFrame.aligned ha) copyPC us um u23 u20 domain
  let quotient := (SszNative.LimbDivision.divideWords divisor (trim words)).1
  have quotientLength : quotient.length = sigWords words := by
    simp only [quotient, SszNative.LimbDivision.divideWords_length, trim_length]
  have v24 : r (.GPR 24#5) v = destination :=
    (loopFrame.registers 24#5 (by decide) (by decide) (by decide) (by decide)).trans u24
  have v22 : r (.GPR 22#5) v = BitVec.ofNat 64 (quotient.length + 1) := by
    rw [quotientLength]
    exact (loopFrame.registers 22#5 (by decide) (by decide) (by decide) (by decide)).trans
      ((copyFrame.registers 22#5 (by decide)).trans h22)
  have vc : CodeAt v base := by simpa only [CodeAt, loopFrame.program] using uc.1
  have ve : read_err v = .None := loopFrame.error.trans (copyFrame.error.trans he)
  have va : CheckSPAlignment v := loopFrame.aligned (copyFrame.aligned ha)
  have vs : NatCompare.Source v destination quotient := by
    have physical : LoopSpace (r (.GPR 31#5) v) destination quotient.length := by
      rw [loopFrame.sp, copyFrame.sp, quotientLength]
      exact ⟨source.1, storage.1, storage.2⟩
    exact physical.source
  have vm : NatCompare.Words v destination quotient := by
    apply words_of_loopWords
    simpa only [u24] using divided
  obtain ⟨scanFuel, t, scanRun, scanFrame, scanPC, zeroStatus, normalizedPointer, normalizedPayload⟩ :=
    quotient_normalization v base destination quotient vc ve va loopPC v24 v22 vs vm
  have loopMemory : MemoryFrame (loopWrites (r (.GPR 31#5) s) destination (sigWords words)) u v := by
    simpa only [copyFrame.sp, u24, trim_length] using loopFrame.memory
  have scanMemory : MemoryFrame (loopWrites (r (.GPR 31#5) s) destination (sigWords words)) v t := by
    apply scanFrame.tight_memory.weaken
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp [loopWrites, loopFrame.sp, copyFrame.sp]
  refine ⟨copyFuel + loopFuel + scanFuel, t, ?_, ?_, scanPC, zeroStatus,
    normalizedPointer, normalizedPayload, ?_, scanFrame.words _ _ vs vm⟩
  · rw [run_plus, run_plus, copyRun, loopRun, scanRun]
  · refine ⟨scanFrame.program.trans (loopFrame.program.trans copyFrame.program),
      scanFrame.error.trans (loopFrame.error.trans copyFrame.error), ?_, ?_,
      (copyFrame.tight_memory.trans loopMemory).trans scanMemory⟩
    · intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        exact (scanFrame.registers _ (by decide)).trans
          ((loopFrame.registers _ (by decide) (by decide) (by decide) (by decide)).trans
            (copyFrame.registers _ (by decide)))
    · intro reg
      exact (scanFrame.vectors reg).trans ((loopFrame.sfp reg).trans (copyFrame.vectors reg))
  · rw [scanFrame.registers 1#5 (by decide)]
    exact remainder

end SszArm.NatDivision
