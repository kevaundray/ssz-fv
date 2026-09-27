import SszArm.ByteViewListExec

namespace SszArm.ByteView.Bounded

open UintCodec
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem width_spill_mem_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (addr : BitVec 64) (value : BitVec (n * 8)) :
    (write_mem_bytes n addr value (w f v s)).mem =
      (write_mem_bytes n addr value s).mem :=
  mem_write_mem_bytes_of_mem_eq (ArmState.mem_w_eq_mem f v s) n addr value

theorem width_read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m : Nat) (addr dst : BitVec 64) (value : BitVec (m * 8)) :
    read_mem_bytes n addr (write_mem_bytes m dst value (w f v s)) =
      read_mem_bytes n addr (write_mem_bytes m dst value s) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp (width_spill_mem_w s f v m dst value)) n addr

def scanOps : List Op :=
  [.p728, .p732, .p736, .p740, .p744, .p748, .p752, .p756, .p760, .p764]

def scanState (s : ArmState) (base word : BitVec 64) : ArmState :=
  w .PC (if word = 0#64 then base + 720#64 else base + 768#64)
    (w (.GPR 11#5) (r (.GPR 11#5) s - 1#64)
      (w (.GPR 12#5) word (widthSaved s)))

theorem scanState_frame (s : ArmState) (base word : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) : WidthFrame s (scanState s base word) := by
  have hf := widthSaved_frame s hs
  constructor
  · simpa [scanState, state_simp_rules] using hf.program
  · simpa [scanState, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simpa (disch := simp_all) [scanState, state_simp_rules] using
      hf.registers reg (by simpa using hr)
  · intro reg; simpa [scanState, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [scanState, state_simp_rules] using hf.memory a ha

theorem scan_read (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 728#64)
    (h8 : r (.GPR 8#5) s = pointer) (h11 : r (.GPR 11#5) s = BitVec.ofNat 64 n)
    (hn : n < words.length) (hs : Source s pointer words)
    (hm : WidthWords s pointer words) :
    run 10 s = scanState s base (words[n]?.getD 0#64) := by
  have hsp := hs.1
  have hlen : words.length < 2^64 := by have := hs.2.1; omega
  have hshift : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8*n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have hload : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8*n)) (widthSaved s) =
      words[n]?.getD 0#64 := by
    have hl := (widthSaved_frame s hsp).byteWords pointer words hs hm ⟨n, hn⟩
    simpa [List.getElem?_eq_getElem hn] using hl
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (widthSaved s) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hf : Follows base scanOps s := by
    change r .PC s = _ at hp
    simp [scanOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hp, BitVec.add_assoc]
  rw [show 10 = scanOps.length by rfl, block_run base scanOps s hc he ha hf]
  simp only [widthSaved] at hload hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h31 : reg = 31#5
      · subst reg
        simp_all (config := {decide := true, instances := true})
          [block, scanOps, Op.effect, put, next, scanState, widthSaved,
           state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
      · by_cases h9 : reg = 9#5
        · subst reg
          simp_all (config := {decide := true, instances := true})
            [block, scanOps, Op.effect, put, next, scanState, widthSaved,
             state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
        · by_cases h11reg : reg = 11#5 <;> by_cases h10reg : reg = 10#5 <;>
            by_cases h12reg : reg = 12#5 <;> (try subst reg) <;>
            simp_all (config := {decide := true, instances := true})
              [block, scanOps, Op.effect, put, next, scanState, widthSaved,
               state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
    | SFP reg =>
      simp [block, scanOps, Op.effect, put, next, scanState, widthSaved, state_simp_rules]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [block, scanOps, Op.effect, put, next, scanState, widthSaved,
         state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
    | FLAG flag =>
      simp [block, scanOps, Op.effect, put, next, scanState, widthSaved, state_simp_rules]
    | ERR =>
      simp [block, scanOps, Op.effect, put, next, scanState, widthSaved, state_simp_rules]
  · simp [block, scanOps, Op.effect, put, next, scanState, widthSaved, state_simp_rules]
  · intro n addr
    simp [block, scanOps, Op.effect, put, next, scanState, widthSaved,
      state_simp_rules, width_read_spill_w]


def scanExit (base : BitVec 64) (count : Nat) : BitVec 64 :=
  if count = 0 then base + 3480#64 else base + 772#64

private theorem count_z (x : BitVec 64) :
    (AddWithCarry x 1#64 0#1).2.z = 1#1 ↔ x + 1#64 = 0#64 := by
  change (if (AddWithCarry x 1#64 0#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_add]
  simp

/-- A descending scan over any stored Large representation, including empty and
redundant high-zero slices. Every recursive step executes its lowering save. -/
theorem scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 720#64 →
    r (.GPR 8#5) s = pointer →
    r (.GPR 11#5) s = BitVec.ofNat 64 n - 1#64 →
    Source s pointer words → WidthWords s pointer words →
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 10#5) t = r (.GPR 10#5) s ∧
      read_pc t = scanExit base (significantCount words n) ∧
      (significantCount words n ≠ 0 → r (.GPR 11#5) t = BitVec.ofNat 64 (significantCount words n)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 h11 hs hm
    let t := block base [.p720, .p724] s
    have hz : (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2.z = 1#1 := by
      apply (count_z _).mpr
      simp [h11]
    refine ⟨2, t, block_run base [.p720, .p724] s hc he ha ?_,
      readonly_frame base _ s (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · change r .PC s = _ at hp
      simp [Follows, Op.row, Op.effect, next, state_simp_rules, BitVec.add_assoc, hp]
    · simp [t, block, Op.effect, next, state_simp_rules]
    · simp [t, block, Op.effect, next, state_simp_rules]
    · simp [t, block, Op.effect, next, state_simp_rules]
    · simp [t, block, Op.effect, next, state_simp_rules, hz, scanExit, significantCount]
    · simp [significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h8 h11 hs hm
    have hlen : words.length < 2^64 := by have := hs.2.1; omega
    have h11' : r (.GPR 11#5) s = BitVec.ofNat 64 n := by rw [h11]; bv_omega
    have hz : (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2.z ≠ 1#1 := by
      intro hz
      have hz' := (count_z (r (.GPR 11#5) s)).mp hz
      rw [h11'] at hz'
      bv_omega
    let u := block base [.p720, .p724] s
    have hu : run 2 s = u := by
      apply block_run base [.p720, .p724] s hc he ha
      change r .PC s = _ at hp
      simp [Follows, Op.row, Op.effect, next, state_simp_rules, BitVec.add_assoc, hp]
    have huf : WidthFrame s u := readonly_frame base _ s (by decide)
    have hup : read_pc u = base + 728#64 := by
      simp [u, block, Op.effect, next, state_simp_rules, hz]
    have hu8 : r (.GPR 8#5) u = pointer := by
      simpa [u, block, Op.effect, next, state_simp_rules] using h8
    have hu11 : r (.GPR 11#5) u = BitVec.ofNat 64 n := by
      simpa [u, block, Op.effect, next, state_simp_rules] using h11'
    have hu9 : r (.GPR 9#5) u = r (.GPR 9#5) s := by
      simp [u, block, Op.effect, next, state_simp_rules]
    have hu10 : r (.GPR 10#5) u = r (.GPR 10#5) s := by
      simp [u, block, Op.effect, next, state_simp_rules]
    let v := scanState u base (words[n]?.getD 0#64)
    have hv : run 10 u = v := scan_read u base pointer words n
      (by simpa only [CodeAt, huf.program] using hc)
      (huf.error.trans he) (huf.aligned ha) hup hu8 hu11 (by omega)
      (huf.byteSource _ _ hs) (huf.byteWords _ _ hs hm)
    have husp : r (.GPR 31#5) u = r (.GPR 31#5) s := huf.sp
    have hss : 16 ≤ (r (.GPR 31#5) s).toNat := hs.1
    have hvf : WidthFrame s v := huf.trans (scanState_frame u base _ (by simpa only [husp] using hss))
    have hv8 : r (.GPR 8#5) v = pointer := by
      simpa [v, scanState, widthSaved, state_simp_rules] using hu8
    have hv9 : r (.GPR 9#5) v = r (.GPR 9#5) s := by
      simpa [v, scanState, widthSaved, state_simp_rules] using hu9
    have hv10 : r (.GPR 10#5) v = r (.GPR 10#5) s := by
      simpa [v, scanState, widthSaved, state_simp_rules] using hu10
    have hv11 : r (.GPR 11#5) v = BitVec.ofNat 64 n - 1#64 := by
      simp [v, scanState, widthSaved, state_simp_rules, hu11]
    have hvs : run 12 s = v := by rw [show 12 = 2 + 10 by decide, run_plus, hu, hv]
    have hsucc : significantCount words (n + 1) =
        if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl
    by_cases hw : words[n]?.getD 0#64 = 0#64
    · have hvp : read_pc v = base + 720#64 := by simp [v, scanState, state_simp_rules, hw]
      obtain ⟨fuel, t, ht, htf, ht8, ht9, ht10, htp, ht11⟩ := ih v (by omega)
        (by simpa only [CodeAt, hvf.program] using hc) (hvf.error.trans he)
        (hvf.aligned ha) hvp hv8 hv11 (hvf.byteSource _ _ hs) (hvf.byteWords _ _ hs hm)
      refine ⟨12 + fuel, t, ?_, hvf.trans htf, ht8.trans (hv8.trans h8.symm),
        ht9.trans hv9, ht10.trans hv10, ?_, ?_⟩
      · rw [run_plus, hvs, ht]
      · simpa only [hsucc, hw, ↓reduceIte] using htp
      · simpa only [hsucc, hw, ↓reduceIte] using ht11
    · have hvp : read_pc v = base + 768#64 := by simp [v, scanState, state_simp_rules, hw]
      let t := block base [.p768] v
      have ht : run 1 v = t := block_run base [.p768] v
        (by simpa only [CodeAt, hvf.program] using hc) (hvf.error.trans he) (hvf.aligned ha)
        (by simpa [Follows, Op.row] using hvp)
      have htf : WidthFrame v t := readonly_frame base [.p768] v (by decide)
      refine ⟨13, t, ?_, hvf.trans htf, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show 13 = 12 + 1 by decide, run_plus, hvs, ht]
      · simpa [t, block, Op.effect, put, next, state_simp_rules] using hv8.trans h8.symm
      · simpa [t, block, Op.effect, put, next, state_simp_rules] using hv9
      · simpa [t, block, Op.effect, put, next, state_simp_rules] using hv10
      · have hvpc : r .PC v = base + 768#64 := hvp
        simp [t, block, Op.effect, put, next, state_simp_rules, hsucc, hw,
          scanExit, hvpc, BitVec.add_assoc]
      · intro _
        simp only [t, block, List.foldl_cons, List.foldl_nil, Op.effect,
          put, next, state_simp_rules, hv11, hsucc, hw, ↓reduceIte]
        simp only [BitVec.ofNat_eq_ofNat, state_simp_rules]
        change BitVec.ofNat 64 n - 1#64 + 2#64 = BitVec.ofNat 64 (n + 1)
        bv_omega

end SszArm.ByteView.Bounded
