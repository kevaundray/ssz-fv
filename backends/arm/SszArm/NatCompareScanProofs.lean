import SszArm.NatCompareScanMixed

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem scan_round (s : ArmState) (base : BitVec 64) (kind : ScanKind)
    (xs ys : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.head)
    (h9 : r (.GPR 9#5) s = kind.index (n + 1))
    (hx : n < xs.length) (hy : n < ys.length) (hi : ScanInputs s kind xs ys) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧ r (.GPR 9#5) t = kind.index n ∧
      r (.GPR 8#5) t = xs[n]?.getD 0#64 ∧ r (.GPR 10#5) t = ys[n]?.getD 0#64 ∧
      read_pc t = if xs[n]?.getD 0#64 = ys[n]?.getD 0#64
        then base + BitVec.ofNat 64 kind.head else base + 548#64 := by
  cases kind with
  | largeLarge =>
    have h9' : r (.GPR 9#5) s = BitVec.ofNat 64 n := by
      simpa [ScanKind.index, BitVec.ofNat_add, BitVec.add_sub_cancel] using h9
    simpa [ScanKind.head, ScanKind.index] using scan_large_round s base xs ys n hc he ha hp h9' hx hy hi
  | largeSmall =>
    have hys : ys = [r (.GPR 3#5) s] := hi.2.1.small (by simpa [ScanKind.rightSmall] using hi.2.2.2)
    have hn : n = 0 := by simp only [hys, List.length_cons, List.length_nil] at hy; omega
    subst n
    simpa [mixedKind, ScanKind.head, ScanKind.index] using
      scan_mixed_round s base xs ys false hc he ha hp (by simpa [ScanKind.index] using h9) hx hy hi
  | smallLarge =>
    have hxs : xs = [r (.GPR 1#5) s] := hi.1.small (by simpa [ScanKind.leftSmall] using hi.2.2.1)
    have hn : n = 0 := by simp only [hxs, List.length_cons, List.length_nil] at hx; omega
    subst n
    simpa [mixedKind, ScanKind.head, ScanKind.index] using
      scan_mixed_round s base xs ys true hc he ha hp (by simpa [ScanKind.index] using h9) hx hy hi
  | smallSmall =>
    have hxs : xs = [r (.GPR 1#5) s] := hi.1.small (by simpa [ScanKind.leftSmall] using hi.2.2.1)
    have hn : n = 0 := by simp only [hxs, List.length_cons, List.length_nil] at hx; omega
    subst n
    simpa [ScanKind.head, ScanKind.index] using
      scan_small_round s base xs ys hc he ha hp (by simpa [ScanKind.index] using h9) hi

/-- Every descending loop terminates through its original RET. -/
theorem scan (base : BitVec 64) (kind : ScanKind) (xs ys : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ xs.length → n ≤ ys.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + BitVec.ofNat 64 kind.head →
    r (.GPR 9#5) s = kind.index n → ScanInputs s kind xs ys →
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 = orderingByte (scanDesc xs ys n) := by
  intro n
  induction n with
  | zero =>
    intro s hx hy hc he ha hp h9 hi
    exact scan_empty s base kind hc he ha hp h9
  | succ n ih =>
    intro s hx hy hc he ha hp h9 hi
    obtain ⟨fuel, u, hu, huf, hu0, hu9, hu8, hu10, hup⟩ :=
      scan_round s base kind xs ys n hc he ha hp h9 (by omega) (by omega) hi
    by_cases hw : xs[n]?.getD 0#64 = ys[n]?.getD 0#64
    · have hup' : read_pc u = base + BitVec.ofNat 64 kind.head := by simpa only [hw, ↓reduceIte] using hup
      obtain ⟨extra, t, ht, htf, htp, hret⟩ := ih u (by omega) (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup' hu9 (ScanInputs.frame huf hu0 hi)
      refine ⟨fuel + extra, t, ?_, huf.trans htf,
        htp.trans (huf.registers 30#5 (by decide)), ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [scanDesc, hw] using hret
    · have hup' : read_pc u = base + 548#64 := by simpa only [hw, ↓reduceIte] using hup
      obtain ⟨extra, t, ht, htf, htp, hret⟩ := return_order u base
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup'
      refine ⟨fuel + extra, t, ?_, huf.trans htf,
        htp.trans (huf.registers 30#5 (by decide)), ?_⟩
      · rw [run_plus, hu, ht]
      · have hne : compare (xs[n]?.getD 0#64).toNat (ys[n]?.getD 0#64).toNat ≠ .eq := by
          intro h
          exact hw (BitVec.eq_of_toNat_eq (Nat.compare_eq_eq.mp h))
        have hret' : (r (.GPR 0#5) t).setWidth 8 =
            orderingByte (compare (xs[n]?.getD 0#64).toNat (ys[n]?.getD 0#64).toNat) := by
          simpa only [hu8, hu10] using hret
        cases hcmp : compare (xs[n]?.getD 0#64).toNat (ys[n]?.getD 0#64).toNat <;>
          simp_all [scanDesc]

end SszArm.NatCompare
