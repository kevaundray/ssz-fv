import SszArm.SerializeSizeFrame
import SszArm.NatCompareOrder

namespace SszArm.Serialize.Size

open SszNative.Limbs

def guardOps : List Serialize.Op := [.p160, .p164]
def tailOps : List Serialize.Op := [.p200, .p204, .p208]

def roundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  Serialize.block base tailOps (loadResult (Serialize.block base guardOps s) base limb)

theorem scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (code : Serialize.CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 160#64) (address : r (.GPR 8#5) s = pointer)
    (valid : n < words.length) (index : r (.GPR 10#5) s = BitVec.ofNat 64 n)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    let t := roundResult s base (words[n]?.getD 0#64)
    run 13 s = t ∧ Frame s t ∧
      r (.GPR 5#5) t = r (.GPR 5#5) s ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then 160 else 212) := by
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have nonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := Serialize.block base guardOps s
  have pc' : r .PC s = base + 160#64 := pc
  have follows : Serialize.Follows base guardOps s := by
    simp [guardOps, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
      Serialize.put, Serialize.next, state_simp_rules, pc', BitVec.add_assoc]
  have runGuard : run 2 s = u := Serialize.block_run base guardOps s code error aligned follows
  have guardFrame : Frame s u := readonly_frame base _ s (by decide)
  have pcU : read_pc u = base + 168#64 := by
    simp [u, guardOps, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
      state_simp_rules, index, nonzero]
  have indexU : r (.GPR 10#5) u = BitVec.ofNat 64 n := by
    simpa [u, guardOps, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
      state_simp_rules] using index
  have addressU : r (.GPR 8#5) u = pointer := (guardFrame.registers _ (by decide)).trans address
  have sourceU := guardFrame.source pointer words source
  have storedU := guardFrame.words pointer words source stored
  have loaded : read_mem_bytes 8 (r (.GPR 8#5) u + (r (.GPR 10#5) u <<< 3))
      (NatCompare.saved u 9#5) = words[n]?.getD 0#64 := by
    rw [indexU, addressU]
    exact NatCompare.limb_load u pointer words n 9#5 valid sourceU storedU
  let v := loadResult u base (words[n]?.getD 0#64)
  have runLoad : run 8 u = v := load_run u base _ (guardFrame.code code)
    (guardFrame.error.trans error) (guardFrame.aligned aligned) pcU sourceU.1 loaded
  have totalFrame : Frame s v := guardFrame.trans (load_frame u base _ sourceU.1)
  have tailFollows : Serialize.Follows base tailOps v := by
    simp [v, tailOps, loadResult, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
      Serialize.put, Serialize.next, state_simp_rules, BitVec.add_assoc]
  have runTail : run 3 v = Serialize.block base tailOps v :=
    Serialize.block_run base tailOps v (totalFrame.code code) (totalFrame.error.trans error)
      (totalFrame.aligned aligned) tailFollows
  refine ⟨?_, totalFrame.trans (readonly_frame base _ v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, runGuard, runLoad, runTail]
    rfl
  all_goals simp [roundResult, tailOps, loadResult, guardOps, Serialize.block,
    Serialize.Op.effect, Serialize.put, Serialize.next, NatCompare.saved,
    state_simp_rules, index, apply_ite]

/-- The original countdown scans every redundant high zero, including a zero-length large operand. -/
theorem significant_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      Serialize.CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 160#64 → r (.GPR 8#5) s = pointer →
      r (.GPR 10#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ Frame s t ∧
        r (.GPR 5#5) t = r (.GPR 5#5) s ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then 416 else 212) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s valid code error aligned pc address index source stored
    let t := Serialize.block base guardOps s
    have pc' : r .PC s = base + 160#64 := pc
    have follows : Serialize.Follows base guardOps s := by
      simp [guardOps, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
        Serialize.put, Serialize.next, state_simp_rules, pc', BitVec.add_assoc]
    refine ⟨2, t, Serialize.block_run base guardOps s code error aligned follows,
      readonly_frame base _ s (by decide), ?_, ?_, ?_⟩
    · simp [t, guardOps, Serialize.block, Serialize.Op.effect, Serialize.put, Serialize.next,
        state_simp_rules]
    · simp [t, guardOps, significantCount, Serialize.block, Serialize.Op.effect,
        Serialize.put, Serialize.next, state_simp_rules, index]
    · simp [significantCount]
  | succ n ih =>
    intro s valid code error aligned pc address index source stored
    have index' : r (.GPR 10#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using index
    obtain ⟨executed, frame, payload, indexU, top, pcU⟩ :=
      scan_round s base pointer words n code error aligned pc address (by omega) index' source stored
    let u := roundResult s base (words[n]?.getD 0#64)
    change run 13 s = u at executed
    change Frame s u at frame
    change r (.GPR 5#5) u = r (.GPR 5#5) s at payload
    change r (.GPR 10#5) u = BitVec.ofNat 64 n - 1#64 at indexU
    change r (.GPR 9#5) u = BitVec.ofNat 64 n at top
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then 160 else 212) at pcU
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, executedT, frameT, payloadT, pcT, topT⟩ := ih u (by omega)
        (frame.code code) (frame.error.trans error) (frame.aligned aligned)
        (by simpa [zero] using pcU) ((frame.registers _ (by decide)).trans address)
        indexU (frame.source _ _ source) (frame.words _ _ source stored)
      refine ⟨13 + fuel, t, ?_, frame.trans frameT, payloadT.trans payload, ?_, ?_⟩
      · rw [run_plus, executed, executedT]
      · simpa [significantCount, zero] using pcT
      · simpa [significantCount, zero] using topT
    · refine ⟨13, u, executed, frame, payload, ?_, ?_⟩
      · simpa [significantCount, zero] using pcU
      · intro positive
        simpa [significantCount, zero] using top

end SszArm.Serialize.Size
