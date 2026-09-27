import SszArm.NatCompareScanRound
import SszArm.ByteViewListBlocks

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def mixedKind (smallLeft : Bool) : ScanKind := if smallLeft then .smallLarge else .largeSmall

def mixedLoad (smallLeft : Bool) : LoadKind := if smallLeft then .smallRight else .leftSmall

def mixedPre (smallLeft : Bool) : List Op :=
  if smallLeft then [.p612, .p616, .p620, .p624, .p628, .p632, .p636]
  else [.p508, .p512, .p516, .p520]

def mixedPost (smallLeft : Bool) : List Op :=
  if smallLeft then [.p672, .p600, .p604, .p608] else [.p488, .p492, .p496, .p500, .p504]

/-- Equal significant lengths with one Small input leave at most one occupied
word. This is the real mixed-representation path, not a redirected Large path. -/
theorem scan_mixed_round (s : ArmState) (base : BitVec 64)
    (xs ys : List (BitVec 64)) (smallLeft : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (mixedKind smallLeft).head)
    (h9 : r (.GPR 9#5) s = 0#64)
    (hx : 0 < xs.length) (hy : 0 < ys.length)
    (hi : ScanInputs s (mixedKind smallLeft) xs ys) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 9#5) t = 0#64 - 1#64 ∧
      r (.GPR 8#5) t = xs[0]?.getD 0 ∧ r (.GPR 10#5) t = ys[0]?.getD 0 ∧
      read_pc t = if xs[0]?.getD 0 = ys[0]?.getD 0
        then base + BitVec.ofNat 64 (mixedKind smallLeft).head else base + 548#64 := by
  let pointer := if smallLeft then r (.GPR 2#5) s else r (.GPR 0#5) s
  let payload := if smallLeft then r (.GPR 3#5) s else r (.GPR 1#5) s
  let words := if smallLeft then ys else xs
  have ho : Operand s pointer payload words := by
    cases smallLeft
    · exact hi.1
    · exact hi.2.1
  have hn : pointer ≠ 0#64 := by
    cases smallLeft
    · simpa [pointer, mixedKind, ScanKind.leftSmall] using hi.2.2.1
    · simpa [pointer, mixedKind, ScanKind.rightSmall] using hi.2.2.2
  obtain ⟨hcount, hs, hm⟩ := ho.large hn
  have hwords : 0 < words.length := by cases smallLeft <;> assumption
  have hpayload : payload.toNat ≠ 0 := by omega
  have hsmall : if smallLeft then xs = [r (.GPR 1#5) s] else ys = [r (.GPR 3#5) s] := by
    cases smallLeft
    · exact hi.2.1.small (by simpa [mixedKind, ScanKind.rightSmall] using hi.2.2.2)
    · exact hi.1.small (by simpa [mixedKind, ScanKind.leftSmall] using hi.2.2.1)
  let u := block base (mixedPre smallLeft) s
  have hpc : r .PC s = base + BitVec.ofNat 64 (mixedKind smallLeft).head := hp
  have hfollow : Follows base (mixedPre smallLeft) s := by
    cases smallLeft <;>
      simp_all [mixedPre, mixedKind, ScanKind.head, Follows, Op.row, Op.effect,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules,
        BitVec.add_assoc, Udivti3.cmp_carry, payload]
  have hu := block_run base (mixedPre smallLeft) s hc he ha hfollow
  have huf : Frame s u := readonly_frame base _ _ (by cases smallLeft <;> decide)
  have hup : read_pc u = base + BitVec.ofNat 64 (mixedLoad smallLeft).start := by
    cases smallLeft <;>
      simp_all [u, mixedPre, mixedLoad, LoadKind.start, block, Op.effect,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules,
        Udivti3.cmp_carry, payload]
  have hload : read_mem_bytes 8
      (r (.GPR (mixedLoad smallLeft).ptr) u + (r (.GPR (mixedLoad smallLeft).index) u <<< 3))
      (saved u (mixedLoad smallLeft).tmp) = words[0]?.getD 0 := by
    have hl := limb_load u pointer words 0 (mixedLoad smallLeft).tmp hwords
      (huf.source _ _ hs) (huf.words _ _ hs hm)
    cases smallLeft <;>
      simpa [u, mixedPre, mixedLoad, LoadKind.ptr, LoadKind.index, LoadKind.tmp,
        block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, pointer, h9] using hl
  let v := loadResult u base (mixedLoad smallLeft) (words[0]?.getD 0)
  have hv : run 8 u = v := load_run u base _ (mixedLoad smallLeft)
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup (huf.source _ _ hs).1 hload
  have hvf : Frame s v := huf.trans (load_frame u base _ (mixedLoad smallLeft) (huf.source _ _ hs).1)
  let t := block base (mixedPost smallLeft) v
  have hpost : Follows base (mixedPost smallLeft) v := by
    cases smallLeft <;>
      simp [mixedPost, v, mixedLoad, loadResult, LoadKind.start, LoadKind.dst,
        Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, BitVec.add_assoc]
  have ht := block_run base (mixedPost smallLeft) v (hvf.code hc)
    (hvf.error.trans he) (hvf.aligned ha) hpost
  refine ⟨(mixedPre smallLeft).length + 8 + (mixedPost smallLeft).length, t, ?_,
    hvf.trans (readonly_frame base _ _ (by cases smallLeft <;> decide)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_plus, run_plus, hu, hv, ht]
  all_goals
    cases smallLeft <;>
      simp_all [t, mixedPost, v, mixedLoad, u, mixedPre, mixedKind, ScanKind.head,
        loadResult, LoadKind.dst, saved, words, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, Udivti3.cmp_zero]

/-- The final Small/Small iteration is a SUBS/CSEL sequence without memory access. -/
theorem scan_small_round (s : ArmState) (base : BitVec 64)
    (xs ys : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 696#64) (h9 : r (.GPR 9#5) s = 1#64)
    (hi : ScanInputs s .smallSmall xs ys) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧ r (.GPR 9#5) t = 0#64 ∧
      r (.GPR 8#5) t = xs[0]?.getD 0 ∧ r (.GPR 10#5) t = ys[0]?.getD 0 ∧
      read_pc t = if xs[0]?.getD 0 = ys[0]?.getD 0 then base + 696#64 else base + 548#64 := by
  have hx : xs = [r (.GPR 1#5) s] := hi.1.small (by simpa [ScanKind.leftSmall] using hi.2.2.1)
  have hy : ys = [r (.GPR 3#5) s] := hi.2.1.small (by simpa [ScanKind.rightSmall] using hi.2.2.2)
  let ops : List Op := [.p696, .p676, .p680, .p684, .p688, .p692]
  let t := block base ops s
  have hpc : r .PC s = base + 696#64 := hp
  have hfollow : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, hpc, h9, BitVec.add_assoc]
  refine ⟨6, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s (by decide), ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [t, ops, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, h9, hx, hy, Udivti3.cmp_zero]

end SszArm.NatCompare
