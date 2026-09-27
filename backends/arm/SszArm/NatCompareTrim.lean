import SszArm.NatCompareBlocks

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def trimHead (right : Bool) : Nat := if right then 76 else 12
def trimCountReg (right : Bool) : BitVec 5 := if right then 10#5 else 9#5
def trimRememberReg (right : Bool) : BitVec 5 := if right then 11#5 else 10#5
def trimKind (right : Bool) : LoadKind := if right then .trimRight else .trimLeft
def trimGuard (right : Bool) : Op := if right then .p76 else .p12
def trimTail (right : Bool) : List Op :=
  if right then [.p112, .p116, .p120] else [.p48, .p52, .p56]
def trimLast (right : Bool) : Op := if right then .p124 else .p60
def trimExit (right : Bool) (count : Nat) : Nat :=
  if right then (if count = 0 then 264 else 128) else 64

def trimRoundState (s : ArmState) (base word : BitVec 64) (right : Bool) : ArmState :=
  block base (trimTail right)
    (loadResult ((trimGuard right).effect base s) base (trimKind right) word)

/-- One occupied countdown round. The indexed read is certified independently
of the countdown arithmetic, and its scratch store is included in the frame. -/
theorem trim_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat) (right : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (trimHead right))
    (h8 : r (.GPR 8#5) s = pointer - 8#64)
    (hn : n < words.length)
    (hcount : r (.GPR (trimCountReg right)) s = BitVec.ofNat 64 (n + 1))
    (hs : Source s pointer words) (hm : Words s pointer words) :
    let t := trimRoundState s base (words[n]?.getD 0#64) right
    run 12 s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR (trimCountReg right)) t = BitVec.ofNat 64 n ∧
      r (.GPR (trimRememberReg right)) t = BitVec.ofNat 64 n ∧
      (right = true → r (.GPR 9#5) t = r (.GPR 9#5) s) ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then trimHead right else if right then 124 else 60) := by
  have hlen : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by bv_omega
  let u := (trimGuard right).effect base s
  have hu : run 1 s = u := by
    change stepi s = u
    exact step s base (trimGuard right) hc (by cases right <;> simpa [trimHead, trimGuard, Op.row] using hp) he ha
  have huf : Frame s u := by
    exact readonly_frame base [trimGuard right] s (by cases right <;> decide)
  have hup : read_pc u = base + BitVec.ofNat 64 (trimKind right).start := by
    cases right <;> simp_all [u, trimGuard, trimHead, trimKind, trimCountReg,
      LoadKind.start, Op.effect, state_simp_rules]
  have hus : Source u pointer words := huf.source _ _ hs
  have hum : Words u pointer words := huf.words _ _ hs hm
  have hucount : r (.GPR (trimCountReg right)) u = BitVec.ofNat 64 (n + 1) := by
    cases right <;> simpa [u, trimGuard, trimCountReg, Op.effect, state_simp_rules] using hcount
  have hu8 : r (.GPR 8#5) u = pointer - 8#64 := by
    cases right <;> simpa [u, trimGuard, Op.effect, state_simp_rules] using h8
  have haddress : pointer - 8#64 + (BitVec.ofNat 64 (n + 1) <<< 3) =
      pointer + (BitVec.ofNat 64 n <<< 3) := by bv_omega
  have hload : read_mem_bytes 8
      (r (.GPR (trimKind right).ptr) u + (r (.GPR (trimKind right).index) u <<< 3))
      (saved u (trimKind right).tmp) = words[n]?.getD 0#64 := by
    have ha' : r (.GPR (trimKind right).ptr) u + (r (.GPR (trimKind right).index) u <<< 3) =
        pointer + (BitVec.ofNat 64 n <<< 3) := by
      cases right with
      | false =>
        change r (.GPR 9#5) u = BitVec.ofNat 64 (n + 1) at hucount
        change r (.GPR 8#5) u + (r (.GPR 9#5) u <<< 3) = _
        rw [hu8, hucount, haddress]
      | true =>
        change r (.GPR 10#5) u = BitVec.ofNat 64 (n + 1) at hucount
        change r (.GPR 8#5) u + (r (.GPR 10#5) u <<< 3) = _
        rw [hu8, hucount, haddress]
    rw [ha']
    exact limb_load u pointer words n (trimKind right).tmp hn hus hum
  let v := loadResult u base (trimKind right) (words[n]?.getD 0#64)
  have hv : run 8 u = v := load_run u base _ (trimKind right) (huf.code hc)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf : Frame s v := huf.trans (load_frame u base _ (trimKind right) hus.1)
  have hfollow : Follows base (trimTail right) v := by
    cases right <;>
      simp [v, trimKind, trimTail, loadResult, LoadKind.start, LoadKind.dst,
        Follows, Op.row, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]
  have ht := block_run base (trimTail right) v (hvf.code hc) (hvf.error.trans he)
    (hvf.aligned ha) hfollow
  have htf : Frame v (block base (trimTail right) v) :=
    readonly_frame base _ _ (by cases right <;> decide)
  refine ⟨?_, hvf.trans htf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases right <;>
      rw [show 12 = 1 + 8 + 3 by decide, run_plus, run_plus, hu, hv]
    all_goals exact ht
  all_goals
    by_cases hw : words[n]?.getD 0#64 = 0#64 <;> cases right <;>
      simp_all (config := {decide := true, instances := true})
        [trimRoundState, u, v, trimGuard, trimKind, trimTail, trimCountReg,
          trimRememberReg, trimHead, loadResult, LoadKind.start, LoadKind.dst,
          LoadKind.tmp, block, Op.effect, put, next, saved, state_simp_rules,
          BitVec.add_assoc]
    all_goals bv_omega

/-- The literal count-down accepts empty and noncanonical Large slices. -/
theorem trim (base pointer : BitVec 64) (words : List (BitVec 64)) (right : Bool) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + BitVec.ofNat 64 (trimHead right) →
    r (.GPR 8#5) s = pointer - 8#64 →
    r (.GPR (trimCountReg right)) s = BitVec.ofNat 64 n →
    Source s pointer words → Words s pointer words →
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      read_pc t = base + BitVec.ofNat 64 (trimExit right (significantCount words n)) ∧
      (if right then
        r (.GPR 9#5) t = r (.GPR 9#5) s ∧
          (significantCount words n ≠ 0 → r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n))
       else r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words n)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 hcount hs hm
    let t := (trimGuard right).effect base s
    have ht : run 1 s = t := by
      change stepi s = t
      exact step s base (trimGuard right) hc
        (by cases right <;> simpa [trimHead, trimGuard, Op.row] using hp) he ha
    refine ⟨1, t, ht, readonly_frame base [trimGuard right] s (by cases right <;> decide), ?_, ?_, ?_⟩
    all_goals cases right <;>
      simp_all [t, trimGuard, trimCountReg, trimExit, significantCount, Op.effect, state_simp_rules]
  | succ n ih =>
    intro s hn hc he ha hp h8 hcount hs hm
    obtain ⟨hv, hvf, hv0, hv8, hvc, hvr, hv9, hvp⟩ :=
      trim_round s base pointer words n right hc he ha hp h8 (by omega) hcount hs hm
    let v := trimRoundState s base (words[n]?.getD 0#64) right
    change run 12 s = v at hv
    change Frame s v at hvf
    change r (.GPR 0#5) v = r (.GPR 0#5) s at hv0
    change r (.GPR 8#5) v = r (.GPR 8#5) s at hv8
    change r (.GPR (trimCountReg right)) v = BitVec.ofNat 64 n at hvc
    change r (.GPR (trimRememberReg right)) v = BitVec.ofNat 64 n at hvr
    change (right = true → r (.GPR 9#5) v = r (.GPR 9#5) s) at hv9
    change read_pc v = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then trimHead right else if right then 124 else 60) at hvp
    have hsucc : significantCount words (n + 1) =
        if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl
    by_cases hw : words[n]?.getD 0#64 = 0#64
    · have hvp' : read_pc v = base + BitVec.ofNat 64 (trimHead right) := by simpa only [hw, ↓reduceIte] using hvp
      obtain ⟨fuel, t, ht, htf, ht0, htp, htc⟩ := ih v (by omega)
        (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) hvp' (hv8.trans h8) hvc
        (hvf.source _ _ hs) (hvf.words _ _ hs hm)
      refine ⟨12 + fuel, t, ?_, hvf.trans htf, ht0.trans hv0, ?_, ?_⟩
      · rw [run_plus, hv, ht]
      · simpa only [hsucc, hw, ↓reduceIte] using htp
      · cases right
        · simpa only [Bool.false_eq_true, ↓reduceIte, hsucc, hw] using htc
        · simp only [Bool.true_eq, ↓reduceIte] at htc ⊢
          exact ⟨htc.1.trans (hv9 rfl), by simpa only [hsucc, hw, ↓reduceIte] using htc.2⟩
    · let t := (trimLast right).effect base v
      have hlast : read_pc v = base + BitVec.ofNat 64 (trimLast right).row.1 := by
        cases right <;> simpa [hw, trimLast, Op.row] using hvp
      change r .PC v = base + BitVec.ofNat 64 (trimLast right).row.1 at hlast
      have ht : run 1 v = t := by
        change stepi v = t
        exact step v base (trimLast right) (hvf.code hc) hlast (hvf.error.trans he) (hvf.aligned ha)
      have htf : Frame v t := readonly_frame base [trimLast right] v (by cases right <;> decide)
      refine ⟨13, t, ?_, hvf.trans htf, ?_, ?_, ?_⟩
      · rw [show 13 = 12 + 1 by decide, run_plus, hv, ht]
      · exact (block_zero base [trimLast right] v (by cases right <;> decide)).trans hv0
      · cases right <;>
          simp [t, trimLast, trimExit, hsucc, hw, Op.row, Op.effect, put, next,
            state_simp_rules, hlast, read_pc, BitVec.add_assoc]
      · cases right with
        | false =>
          change r (.GPR 10#5) v = BitVec.ofNat 64 n at hvr
          simp [t, trimLast, hsucc, hw, Op.effect, put, next, state_simp_rules,
            hvr, BitVec.ofNat_add]
        | true =>
          change r (.GPR 11#5) v = BitVec.ofNat 64 n at hvr
          have hv9' := hv9 rfl
          simp [t, trimLast, hsucc, hw, Op.effect, put, next, state_simp_rules,
            hvr, hv9', BitVec.ofNat_add]

end SszArm.NatCompare
