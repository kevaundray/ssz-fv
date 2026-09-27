import SszArm.ByteViewListLarge

namespace SszArm.ByteView.Bounded

open UintCodec
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def entryOps (a : BitVec 64) : List Op :=
  [.p688, .p692, .p696] ++
    if a = 0#64 then [.p700, .p704, .p712] else [.p708, .p712]

theorem entry_runs (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 688#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
      r (.GPR 9#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ∧
      r (.GPR 10#5) t = (if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64) ∧
      read_pc t = if read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64
        then base + 2596#64 else base + 716#64 := by
  let ops := entryOps (r (.GPR 3#5) s)
  let t := block base ops s
  have hpc : r .PC s = base + 688#64 := hp
  have hfollow : Follows base ops s := by
    dsimp only [ops]
    by_cases hz : r (.GPR 3#5) s = 0#64 <;>
      simp [entryOps, hz, Follows, Op.row, Op.effect, Vector.widthLoaded,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules,
        Udivti3.cmp_zero, BitVec.ofNat_eq_ofNat, hpc, BitVec.add_assoc]
  refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [ops, entryOps]; split <;> decide
  all_goals
    dsimp only [t, ops]
    by_cases hz : r (.GPR 3#5) s = 0#64 <;>
      simp [entryOps, hz, block, Op.effect, Vector.widthLoaded,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat]

def Post (s : ArmState) (base : BitVec 64) (capacity : Nat) (t : ArmState) : Prop :=
  WidthFrame s t ∧ CheckSPAlignment t ∧
  r (.GPR 8#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
  r (.GPR 9#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ∧
  read_pc t = if (r (.GPR 3#5) s).toNat ≤ capacity then base + 4492#64 else base + 3576#64

theorem small_runs (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 688#64) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hsmall : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64) :
    ∃ fuel, Post s base (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s).toNat (run fuel s) := by
  obtain ⟨fuel, t, ht, hf, h8, h9, _, hpc⟩ := entry_runs s base hc hp he ha
  have htp : read_pc t = base + 2596#64 := by simpa only [hsmall, ↓reduceIte] using hpc
  obtain ⟨extra, u, hu, huf, hu8, hu9, hup⟩ := small_compare t base
    (by simpa only [CodeAt, hf.program] using hc) htp (hf.error.trans he) (hf.aligned ha)
    (by
      have hsp : r (.GPR 31#5) t = r (.GPR 31#5) s := hf.sp
      simpa only [hsp] using hs)
  have hfinal := hf.trans huf
  refine ⟨fuel + extra, ?_⟩
  rw [run_plus, ht, hu]
  refine ⟨hfinal, hfinal.aligned ha, hu8.trans h8, hu9.trans h9, ?_⟩
  simpa only [h9, hf.registers 3#5 (by decide)] using hup

theorem large_runs (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (hp : read_pc s = base + 688#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp0 : pointer ≠ 0#64)
    (hptr : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = pointer)
    (hcount : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = BitVec.ofNat 64 words.length)
    (hs : Source s pointer words) (hm : WidthWords s pointer words) :
    ∃ fuel, Post s base (value words) (run fuel s) := by
  obtain ⟨fuel, t, ht, hf, h8, h9, h10, hpc⟩ := entry_runs s base hc hp he ha
  have htp : read_pc t = base + 716#64 := by simpa only [hptr, hp0, ↓reduceIte] using hpc
  let v := block base [.p716] t
  have hv : run 1 t = v := block_run base [.p716] t
    (by simpa only [CodeAt, hf.program] using hc) (hf.error.trans he) (hf.aligned ha)
    (by simpa [Follows, Op.row] using htp)
  have hvf : WidthFrame s v := hf.trans (readonly_frame base [.p716] t (by decide))
  have hv8 : r (.GPR 8#5) v = pointer := by
    simpa [v, block, Op.effect, put, next, state_simp_rules] using h8.trans hptr
  have hv9 : r (.GPR 9#5) v = BitVec.ofNat 64 words.length := by
    simpa [v, block, Op.effect, put, next, state_simp_rules] using h9.trans hcount
  have hv10 : r (.GPR 10#5) v = if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64 := by
    simpa [v, block, Op.effect, put, next, state_simp_rules] using h10
  have hv11 : r (.GPR 11#5) v = BitVec.ofNat 64 words.length - 1#64 := by
    simp [v, block, Op.effect, put, next, state_simp_rules, h9, hcount]
  have hvp : read_pc v = base + 720#64 := by
    have hpc' : r .PC t = base + 716#64 := htp
    simp [v, block, Op.effect, put, next, state_simp_rules, hpc', BitVec.add_assoc]
  obtain ⟨count, q, hq, hqf, hq8, hq9, hq10, hqp, hq11⟩ := scan base pointer words words.length v
    (Nat.le_refl _) (by simpa only [CodeAt, hvf.program] using hc) (hvf.error.trans he)
    (hvf.aligned ha) hvp hv8 hv11 (hvf.byteSource _ _ hs) (hvf.byteWords _ _ hs hm)
  have hsf := hvf.trans hqf
  have hq10' : r (.GPR 10#5) q = if r (.GPR 3#5) q = 0#64 then 0#64 else 1#64 := by
    rw [hsf.registers 3#5 (by decide)]
    exact hq10.trans hv10
  obtain ⟨extra, u, hu, huf, hu8, hu9, hup⟩ := large_compare q base pointer words
    (by simpa only [CodeAt, hsf.program] using hc) hqp (hsf.error.trans he) (hsf.aligned ha)
    (hq8.trans hv8) (hq9.trans hv9) hq10' hq11
    (hsf.byteSource _ _ hs) (hsf.byteWords _ _ hs hm)
  have hfinal := hsf.trans huf
  refine ⟨fuel + (1 + (count + extra)), ?_⟩
  rw [run_plus, ht, run_plus, hv, run_plus, hq, hu]
  refine ⟨hfinal, hfinal.aligned ha, ?_, ?_, ?_⟩
  · exact hu8.trans (hq8.trans (hv8.trans hptr.symm))
  · exact hu9.trans (hq9.trans (hv9.trans hcount.symm))
  · simpa only [hsf.registers 3#5 (by decide)] using hup

/-- The arbitrary-Nat ByteList limit check. No machine-sized capacity bound and
no canonicality or future-execution premise is required. -/
theorem width_runs (s : ArmState) (base : BitVec 64) (capacity : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 688#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (_hheader : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64)
    (hs : ScratchSeparated s)
    (hwidth : SszNative.NatMemory.At (widthLoad s)
      ((r (.GPR 1#5) s).toNat + 8) capacity) :
    ∃ fuel, Post s base capacity (run fuel s) := by
  rcases hwidth with ⟨⟨hzero, hvalue⟩, hbound⟩ | ⟨pointer, words, hlarge, hvalue⟩
  · have hz : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, BitVec.ofNat_add] using hzero
    have hv : (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s).toNat = capacity := by
      simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc] using hvalue
    simpa only [hv] using small_runs s base hc hp he ha hs.1 hz
  · rcases hlarge with ⟨hpositive, hbound, _halign, hspace, hptr, hcount, hwords⟩
    let p := BitVec.ofNat 64 pointer
    have hpn : p.toNat = pointer := Nat.mod_eq_of_lt hbound
    have hlen : words.length < 2^64 := by omega
    have hn : (BitVec.ofNat 64 words.length).toNat = words.length := Nat.mod_eq_of_lt hlen
    have hp0 : p ≠ 0#64 := by intro h; have := congrArg BitVec.toNat h; simp [hpn] at this; omega
    have h8 : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = p := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, BitVec.ofNat_add, hpn] using hptr
    have h9 : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = BitVec.ofNat 64 words.length := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc, hn] using hcount
    have hsource : Source s p words := by
      refine ⟨hs.1, by simpa only [hpn] using hspace, ?_⟩
      by_cases hz : words = []
      · exact Or.inl hz
      · right
        change p.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
          (r (.GPR 31#5) s).toNat ≤ p.toNat
        have hpos : 0 < words.length := by cases words <;> simp_all
        have hn0 : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
        have hsep := hs.2
        dsimp only at hsep
        simpa only [h8, h9, hn] using
          hsep (by simpa only [h8] using hp0) (by simpa only [h9] using hn0)
    have hm : WidthWords s p words := by
      intro i
      apply BitVec.eq_of_toNat_eq
      have hi := hwords i
      simpa [SszNative.NatMemory.wordsAt, widthLoad, p, BitVec.ofNat_add] using hi
    simpa only [hvalue] using large_runs s base p words hc hp he ha hp0 h8 h9 hsource hm

end SszArm.ByteView.Bounded
