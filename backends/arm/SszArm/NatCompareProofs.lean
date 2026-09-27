import SszArm.NatCompareEntry

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Full entry-to-return refinement of the native length-first algorithm. -/
theorem compare_words (s : ArmState) (base : BitVec 64) (xs ys : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base)
    (hx : Operand s (r (.GPR 0#5) s) (r (.GPR 1#5) s) xs)
    (hy : Operand s (r (.GPR 2#5) s) (r (.GPR 3#5) s) ys) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 = orderingByte (nativeCmp xs ys) := by
  obtain ⟨lf, u, hu, huf, hu0, hu9, hup⟩ := left_width s base xs hc he ha hp hx
  obtain ⟨hux, huy⟩ := huf.operands hu0 xs ys hx hy
  obtain ⟨rf, v, hv, hvf, hv0, hv9, hvp, hv8⟩ := right_width u base ys
    (huf.code hc) (huf.error.trans he) (huf.aligned ha)
    (by simpa only [hu0] using hup) huy
  have hvs : Frame s v := huf.trans hvf
  have hvs0 : r (.GPR 0#5) v = r (.GPR 0#5) s := hv0.trans hu0
  have hvs9 : r (.GPR 9#5) v = BitVec.ofNat 64 (sigWords xs) := hv9.trans hu9
  let kind := rightKind (r (.GPR 2#5) u) (sigWords ys)
  let b := BitVec.ofNat 64 (sigWords ys)
  have hb : if kind = .empty then b = 0#64 else r (.GPR 8#5) v = b := by
    by_cases hz : r (.GPR 2#5) u = 0#64 <;> by_cases hn : sigWords ys = 0
    all_goals simp [kind, rightKind, hz, hn, b] at hv8 ⊢
    all_goals assumption
  obtain ⟨cf, q, hq, hqf, hq0, hq9, hq8, hqp⟩ := length_compare v base b kind
    (hvs.code hc) (hvs.error.trans he) (hvs.aligned ha) hvp hb
  have hqs : Frame s q := hvs.trans hqf
  have hqs0 : r (.GPR 0#5) q = r (.GPR 0#5) s := hq0.trans hvs0
  have hqs9 : r (.GPR 9#5) q = BitVec.ofNat 64 (sigWords xs) := hq9.trans hvs9
  have hrun : run (lf + rf + cf) s = q := by rw [run_plus, run_plus, hu, hv, hq]
  have hxl : sigWords xs < 2^64 := Nat.lt_of_le_of_lt (sigWords_le_length xs) hx.length_bound
  have hyl : sigWords ys < 2^64 := Nat.lt_of_le_of_lt (sigWords_le_length ys) hy.length_bound
  by_cases hequal : sigWords xs = sigWords ys
  · have hbit : r (.GPR 9#5) v = b := by simp only [hvs9, b, hequal]
    have hqp' : read_pc q = base + 304#64 := by simpa only [hbit, ↓reduceIte] using hqp
    obtain ⟨ef, z, hz, hzf, hz0, hz9, hzp⟩ := scan_entry q base (sigWords xs)
      (hqs.code hc) (hqs.error.trans he) (hqs.aligned ha) hqp' hqs9
    obtain ⟨hqx, hqy⟩ := hqs.operands hqs0 xs ys hx hy
    have hinputs := ScanInputs.frame hzf hz0 (scan_inputs q xs ys hqx hqy)
    obtain ⟨sf, t, ht, htf, htp, hret⟩ := scan base
      (scanKind (r (.GPR 0#5) q) (r (.GPR 2#5) q)) xs ys (sigWords xs) z
      (sigWords_le_length xs) (by rw [hequal]; exact sigWords_le_length ys)
      ((hqs.trans hzf).code hc) ((hqs.trans hzf).error.trans he)
      ((hqs.trans hzf).aligned ha) hzp hz9 hinputs
    refine ⟨lf + rf + cf + ef + sf, t, ?_, hqs.trans (hzf.trans htf),
      htp.trans ((hqs.trans hzf).registers 30#5 (by decide)), ?_⟩
    · rw [run_plus, run_plus, hrun, hz, ht]
    · simpa [nativeCmp, hequal] using hret
  · have hbit : r (.GPR 9#5) v ≠ b := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [hvs9] at h'
      exact hequal (by simpa [b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] using h')
    have hqp' : read_pc q = base + 256#64 := by simpa only [hbit, ↓reduceIte] using hqp
    obtain ⟨extra, t, ht, htf, htp, hret⟩ := length_return q base
      (hqs.code hc) (hqs.error.trans he) (hqs.aligned ha) hqp'
    refine ⟨lf + rf + cf + extra, t, ?_, hqs.trans htf,
      htp.trans (hqs.registers 30#5 (by decide)), ?_⟩
    · rw [run_plus, hrun, ht]
    · rw [hret, hq8, orderWord_low, hvs9]
      simp only [b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl]
      have hne : compare (sigWords xs) (sigWords ys) ≠ .eq := by
        intro h; exact hequal (Nat.compare_eq_eq.mp h)
      cases hcmp : compare (sigWords xs) (sigWords ys) <;> simp_all [nativeCmp]

/-- The static slot condition preserves both borrowed input representations,
including an empty Large slice at any non-null aligned address. -/
theorem Frame.pair {s t : ArmState} (hf : Frame s t)
    (pointer payload : BitVec 64) (value : Nat)
    (hi : SszNative.NatMemory.Pair (widthLoad s) pointer payload value)
    (hs : Owned s pointer payload) :
    SszNative.NatMemory.Pair (widthLoad t) pointer payload value := by
  rcases hi with hsmall | ⟨words, hpos, halign, hbound, hcount, hm, hv⟩
  · exact Or.inl hsmall
  · have hn : pointer ≠ 0#64 := by intro h; simp [h] at hpos
    have hsource : Source s pointer words := by
      refine ⟨hs.1, hbound, ?_⟩
      by_cases he : words = []
      · exact Or.inl he
      · right
        have hc : payload ≠ 0#64 := by intro h; cases words <;> simp_all
        simpa only [hcount, BitVec.ofNat_eq_ofNat] using hs.2 hn hc
    have hwords : Words s pointer words := by
      intro i
      apply BitVec.eq_of_toNat_eq
      have hi := Option.some.inj (hm i)
      simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using hi
    refine Or.inr ⟨words, hpos, halign, hbound, hcount, ?_, hv⟩
    intro i
    have hl := (hf.words pointer words hsource hwords) i
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using congrArg (fun v : BitVec 64 => some v.toNat) hl

/-- Kernel-checked native Nat.compare on arbitrary representable operands.
The contract observes exactly Rust Ordering's low byte, the original RET target,
the complete callee-save/SP frame, and unchanged borrowed operands. -/
theorem compare_correct (s : ArmState) (base : BitVec 64) (lhs rhs : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry)
    (hl : SszNative.NatMemory.Pair (widthLoad s) (r (.GPR 0#5) s) (r (.GPR 1#5) s) lhs)
    (hr : SszNative.NatMemory.Pair (widthLoad s) (r (.GPR 2#5) s) (r (.GPR 3#5) s) rhs)
    (hls : Owned s (r (.GPR 0#5) s) (r (.GPR 1#5) s))
    (hrs : Owned s (r (.GPR 2#5) s) (r (.GPR 3#5) s)) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      read_pc t = r (.GPR 30#5) s ∧ read_err t = .None ∧
      r (.GPR 31#5) t = r (.GPR 31#5) s ∧
      (∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 → r (.GPR reg) t = r (.GPR reg) s) ∧
      (r (.GPR 0#5) t).setWidth 8 = orderingByte (compare lhs rhs) ∧
      SszNative.NatMemory.Pair (widthLoad t) (r (.GPR 0#5) s) (r (.GPR 1#5) s) lhs ∧
      SszNative.NatMemory.Pair (widthLoad t) (r (.GPR 2#5) s) (r (.GPR 3#5) s) rhs := by
  obtain ⟨xs, hx, hvx⟩ := Operand.of_pair s _ _ lhs hl hls
  obtain ⟨ys, hy, hvy⟩ := Operand.of_pair s _ _ rhs hr hrs
  obtain ⟨fuel, t, ht, hf, hpc, hret⟩ := compare_words s base xs ys hc he ha
    (by simpa [entry] using hp) hx hy
  refine ⟨fuel, t, ht, hf, hpc, hf.error.trans he, hf.sp, ?_, ?_,
    hf.pair _ _ lhs hl hls, hf.pair _ _ rhs hr hrs⟩
  · intro reg hlo hhi
    apply hf.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> bv_omega
  · simpa only [nativeCmp_correct, hvx, hvy] using hret

end SszArm.NatCompare
