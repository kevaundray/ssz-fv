import SszArm.NatCompareScan

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- One descending comparison with two occupied borrowed limbs. The two arrays
may overlap: only their common lowering-slot separation is used. -/
theorem scan_large_round (s : ArmState) (base : BitVec 64)
    (xs ys : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 364#64)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 n)
    (hx : n < xs.length) (hy : n < ys.length)
    (hi : ScanInputs s .largeLarge xs ys) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 8#5) t = xs[n]?.getD 0 ∧ r (.GPR 10#5) t = ys[n]?.getD 0 ∧
      read_pc t = if xs[n]?.getD 0 = ys[n]?.getD 0 then base + 364#64 else base + 548#64 := by
  have hn0 : r (.GPR 0#5) s ≠ 0#64 := by simpa [ScanKind.leftSmall] using hi.2.2.1
  have hn2 : r (.GPR 2#5) s ≠ 0#64 := by simpa [ScanKind.rightSmall] using hi.2.2.2
  obtain ⟨hc1, hsx, hmx⟩ := hi.1.large hn0
  obtain ⟨hc3, hsy, hmy⟩ := hi.2.1.large hn2
  have hlen := hi.1.length_bound
  have hn : n < 2^64 := by omega
  have hcn : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hlast : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by have := hsx.2.1; bv_omega
  let pre : List Op := [.p364, .p368, .p372, .p376]
  let u := block base pre s
  have hpc : r .PC s = base + 364#64 := hp
  have hu : run 4 s = u := block_run base pre s hc he ha (by
    simp [pre, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, hpc, h9, hlast, hcn, hc1,
      Udivti3.cmp_carry, BitVec.add_assoc, Nat.not_le.mpr hx])
  have huf : Frame s u := readonly_frame base pre s (by decide)
  have hup : read_pc u = base + 380#64 := by
    simp [u, pre, block, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, hlast, h9, hcn, hc1, Udivti3.cmp_carry,
      Nat.not_le.mpr hx]
  have huload : read_mem_bytes 8 (r (.GPR LoadKind.left.ptr) u +
      (r (.GPR LoadKind.left.index) u <<< 3)) (saved u LoadKind.left.tmp) = xs[n]?.getD 0 := by
    have hl := limb_load u (r (.GPR 0#5) s) xs n 10#5 hx (huf.source _ _ hsx) (huf.words _ _ hsx hmx)
    simpa [u, pre, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, h9, LoadKind.ptr, LoadKind.index, LoadKind.tmp] using hl
  let v := loadResult u base .left (xs[n]?.getD 0)
  have hv : run 8 u = v := load_run u base _ .left (huf.code hc)
    (huf.error.trans he) (huf.aligned ha) hup (huf.source _ _ hsx).1 huload
  have hvf : Frame s v := huf.trans (load_frame u base _ .left (huf.source _ _ hsx).1)
  let mid : List Op := [.p412, .p416]
  let w := block base mid v
  have hw : run 2 v = w := block_run base mid v (hvf.code hc)
    (hvf.error.trans he) (hvf.aligned ha) (by
      simp [mid, Follows, v, loadResult, LoadKind.start, LoadKind.dst,
        Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, BitVec.add_assoc])
  have hwf : Frame s w := hvf.trans (readonly_frame base mid v (by decide))
  have hw9 : r (.GPR 9#5) w = BitVec.ofNat 64 n := by
    simp [w, mid, v, u, pre, loadResult, LoadKind.dst, saved, block, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, h9]
  have hw3 : r (.GPR 3#5) v = r (.GPR 3#5) s := hvf.registers _ (by decide)
  have hv9 : r (.GPR 9#5) v = BitVec.ofNat 64 n := by
    simp [v, u, pre, loadResult, LoadKind.dst, saved, block, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, h9]
  have hwp : read_pc w = base + 320#64 := by
    simp [w, mid, block, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, hv9, hw3, hcn, hc3, Udivti3.cmp_carry,
      Nat.not_le.mpr hy]
  have hwload : read_mem_bytes 8 (r (.GPR LoadKind.right.ptr) w +
      (r (.GPR LoadKind.right.index) w <<< 3)) (saved w LoadKind.right.tmp) = ys[n]?.getD 0 := by
    have hl := limb_load w (r (.GPR 2#5) s) ys n 11#5 hy (hwf.source _ _ hsy) (hwf.words _ _ hsy hmy)
    simpa only [LoadKind.ptr, LoadKind.index, LoadKind.tmp, hw9,
      hwf.registers 2#5 (by decide)] using hl
  let z := loadResult w base .right (ys[n]?.getD 0)
  have hz : run 8 w = z := load_run w base _ .right (hwf.code hc)
    (hwf.error.trans he) (hwf.aligned ha) hwp (hwf.source _ _ hsy).1 hwload
  have hzf : Frame s z := hwf.trans (load_frame w base _ .right (hwf.source _ _ hsy).1)
  let post : List Op := [.p352, .p356, .p360]
  let t := block base post z
  have ht : run 3 z = t := block_run base post z (hzf.code hc)
    (hzf.error.trans he) (hzf.aligned ha) (by
      simp [post, Follows, z, loadResult, LoadKind.start, LoadKind.dst,
        Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, BitVec.add_assoc])
  refine ⟨25, t, ?_, hzf.trans (readonly_frame base post z (by decide)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 25 = 4 + 8 + 2 + 8 + 3 by decide, run_plus, run_plus, run_plus,
      run_plus, hu, hv, hw, hz, ht]
  all_goals
    simp [t, post, z, w, mid, v, u, pre, loadResult, LoadKind.dst, saved,
      block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, h9, Udivti3.cmp_zero]

end SszArm.NatCompare
