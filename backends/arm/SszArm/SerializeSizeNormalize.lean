import SszArm.SerializeSizeScan
import SszNatNarrow

namespace SszArm.Serialize.Size

open SszNative (NatOperand)
open SszNative.Limbs

theorem host_bound_iff (words : List (BitVec 64)) :
    value words < 2^64 ↔ sigWords words ≤ 1 := by
  simpa only [NatOperand.wordCount, NatOperand.words, NatOperand.value, Nat.mul_one] using
    ((NatOperand.large 1#64 words).wordCount_le_iff_value_lt 1).symm

theorem low_word (words : List (BitVec 64)) (fits : sigWords words ≤ 1) :
    words[0]?.getD 0#64 = BitVec.ofNat 64 (value words) := by
  have bound := (host_bound_iff words).mpr fits
  cases words with
  | nil => rfl
  | cons first rest =>
    have zero : value rest = 0 := by simp only [value] at bound; omega
    simp [value, zero]

theorem load_low (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (code : Serialize.CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 420#64) (address : r (.GPR 8#5) s = pointer)
    (stored : NatCompare.Words s pointer words) (nonempty : 0 < words.length)
    (fits : sigWords words ≤ 1) :
    ∃ t, run 1 s = t ∧ Frame s t ∧ read_pc t = base + 424#64 ∧
      r (.GPR 5#5) t = BitVec.ofNat 64 (value words) := by
  have first := stored ⟨0, nonempty⟩
  have loaded : read_mem_bytes 8 pointer s = BitVec.ofNat 64 (value words) := by
    have observed : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
      simpa [List.getElem?_eq_getElem nonempty] using first
    rw [observed, low_word words fits]
  let t := Serialize.block base [.p420] s
  refine ⟨t, Serialize.block_run base [.p420] s code error aligned ⟨pc, trivial⟩,
    readonly_frame base _ s (by decide), ?_, ?_⟩
  · change r .PC s = base + 420#64 at pc
    simp [t, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
      state_simp_rules, pc, BitVec.add_assoc]
  · simp [t, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
      state_simp_rules, address, loaded]

/-- All nonempty physical representations exit either at the host error or with
    their mathematical value reloaded into X5. No significant-width premise is assumed. -/
theorem large_ready (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (code : Serialize.CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 160#64) (address : r (.GPR 8#5) s = pointer)
    (count : r (.GPR 5#5) s = BitVec.ofNat 64 words.length)
    (index : r (.GPR 10#5) s = BitVec.ofNat 64 words.length - 1#64)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words)
    (nonempty : 0 < words.length) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      read_pc t = (if value words < 2^64 then base + 424#64 else base + 224#64) ∧
      (value words < 2^64 → r (.GPR 5#5) t = BitVec.ofNat 64 (value words)) := by
  obtain ⟨fuel, u, executed, frame, payload, pcU, top⟩ :=
    significant_scan base pointer words words.length s (Nat.le_refl _) code error aligned
      pc address index source stored
  have countU : r (.GPR 5#5) u = BitVec.ofNat 64 words.length := payload.trans count
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have finishLoad (v : ArmState) (extra : Nat) (runBefore : run extra u = v)
      (beforeFrame : Frame u v) (loadPC : read_pc v = base + 420#64)
      (fits : sigWords words ≤ 1) :
      ∃ total t, run total s = t ∧ Frame s t ∧
        read_pc t = (if value words < 2^64 then base + 424#64 else base + 224#64) ∧
        (value words < 2^64 → r (.GPR 5#5) t = BitVec.ofNat 64 (value words)) := by
    have totalFrame := frame.trans beforeFrame
    obtain ⟨t, runLoad, loadFrame, pcT, valueT⟩ := load_low v base pointer words
      (totalFrame.code code) (totalFrame.error.trans error) (totalFrame.aligned aligned)
      loadPC ((totalFrame.registers _ (by decide)).trans address)
      (totalFrame.words _ _ source stored) nonempty fits
    refine ⟨fuel + extra + 1, t, ?_, totalFrame.trans loadFrame, ?_, fun _ => valueT⟩
    · rw [run_plus, run_plus, executed, runBefore, runLoad]
    · simpa only [if_pos ((host_bound_iff words).mpr fits)] using pcT
  change read_pc u = base + BitVec.ofNat 64 (if sigWords words = 0 then 416 else 212) at pcU
  change sigWords words ≠ 0 → r (.GPR 9#5) u = BitVec.ofNat 64 (sigWords words - 1) at top
  by_cases zero : sigWords words = 0
  · have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
    have zeroPC : read_pc u = base + 416#64 := by simpa [zero] using pcU
    let v := Serialize.block base [.p416] u
    have runBefore : run 1 u = v := Serialize.block_run base [.p416] u
      (frame.code code) (frame.error.trans error) (frame.aligned aligned) ⟨zeroPC, trivial⟩
    apply finishLoad v 1 runBefore (readonly_frame base _ u (by decide))
    · simp [v, Serialize.block, Serialize.Op.effect, state_simp_rules, countU, countNonzero]
    · omega
  · have positive : 0 < sigWords words := by omega
    have sigBound : sigWords words < 2^64 := by have := sigWords_le_length words; omega
    have increment : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    have equal : BitVec.ofNat 64 (sigWords words) = 1#64 ↔ sigWords words = 1 := by bv_omega
    have scanPC : read_pc u = base + 212#64 := by simpa [zero] using pcU
    have scanPC' : r .PC u = base + 212#64 := scanPC
    let ops : List Serialize.Op := [.p212, .p216, .p220]
    let v := Serialize.block base ops u
    have follows : Serialize.Follows base ops u := by
      simp [ops, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
        Serialize.put, Serialize.next, Emit.Dispatch.compare64, Emit.Dispatch.next,
        state_simp_rules, scanPC', BitVec.add_assoc]
    have runBefore : run 3 u = v := Serialize.block_run base ops u (frame.code code)
      (frame.error.trans error) (frame.aligned aligned) follows
    have beforeFrame : Frame u v := readonly_frame base ops u (by decide)
    by_cases fits : sigWords words ≤ 1
    · apply finishLoad v 3 runBefore beforeFrame
      · simp [v, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, top zero,
          increment, equal, show sigWords words = 1 by omega]
      · exact fits
    · have large : ¬ value words < 2^64 := mt (host_bound_iff words).mp fits
      refine ⟨fuel + 3, v, ?_, frame.trans beforeFrame, ?_, fun impossible => False.elim (large impossible)⟩
      · rw [run_plus, executed, runBefore]
      · simp [v, ops, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, top zero,
          increment, equal, show sigWords words ≠ 1 by omega, large]

end SszArm.Serialize.Size
