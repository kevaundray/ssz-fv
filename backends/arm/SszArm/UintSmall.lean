import SszArm.UintByteMemory

namespace SszArm.UintCodec.Small

open SszNative.WordDecode

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private def trimPass : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
private def packPass : List Nat := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

private theorem byte_zero (b : UInt8) :
    (b.toBitVec.setWidth 64).setWidth 32 = 0#32 ↔ b = 0 := by
  rw [UInt8.eq_iff_toBitVec_eq]
  change (b.toBitVec.setWidth 64).setWidth 32 = 0#32 ↔ b.toBitVec = 0#8
  bv_omega

/-- The mask and LSLV signed-modulo semantics agree with the byte shift.
The eight cases are positions, not an enumeration of possible byte values. -/
private theorem byte_shift (i : Nat) (hi : i < 8) :
    (BitVec.ofInt 6 ((BitVec.ofNat 64 (8*i) &&& 56#64).toInt % 64)).toNat = 8*i := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Register updates inside a spill do not change the spill's memory image. -/
private theorem spill_mem_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (addr : BitVec 64) (value : BitVec (n*8)) :
    (write_mem_bytes n addr value (w f v s)).mem =
      (write_mem_bytes n addr value s).mem := by
  exact mem_write_mem_bytes_of_mem_eq (ArmState.mem_w_eq_mem f v s) n addr value

private theorem read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m : Nat) (addr dst : BitVec 64) (value : BitVec (m*8)) :
    read_mem_bytes n addr (write_mem_bytes m dst value (w f v s)) =
      read_mem_bytes n addr (write_mem_bytes m dst value s) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp (spill_mem_w s f v m dst value)) n addr

macro "small_simp" : tactic => `(tactic|
  simp_all (config := {decide := true, instances := true})
    [trimPass, packPass, Follows, block, instruction, Udivti3.next, Udivti3.put,
     Udivti3.compare, Udivti3.branch, state_simp_rules, BitVec.add_assoc,
     BitVec.sub_add_cancel, read_spill_w, apply_ite])

/-- A complete positive-count trip through the actual trimming loop. -/
private theorem trim_pass (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Input s data) (hp : read_pc s = base + 4328#64)
    (n : Nat) (hn : n + 1 ≤ data.size)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (n + 1))
    (h10 : r (.GPR 10) s = r (.GPR 2) s - 1#64) :
    let t := block trimPass s
    run 11 s = t ∧ Stable s t ∧
    read_pc t = (if data[n]?.getD 0 = 0 then base + 4328#64 else base + 4372#64) ∧
    r (.GPR 8) t = BitVec.ofNat 64 n ∧
    r (.GPR 9) t = BitVec.ofNat 64 (n + 1) ∧
    r (.GPR 10) t = r (.GPR 2) t - 1#64 := by
  have hb := hi.bounded
  have hne : r (.GPR 8) s ≠ 0#64 := by bv_omega
  have haddr : r (.GPR 2) s - 1#64 + BitVec.ofNat 64 (n+1) =
      r (.GPR 2) s + BitVec.ofNat 64 n := by bv_omega
  have hdec : BitVec.ofNat 64 (n+1) - 1#64 = BitVec.ofNat 64 n := by bv_omega
  have hl := scratch_byte s data hi n (by omega)
  have hr := scratch_restore s hi.stack
  have hz := byte_zero (data[n]?.getD 0)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact follows_run base trimPass s hc he ha (by small_simp)
  · constructor
    · small_simp
    · small_simp
    · intro i h
      simp only [Live] at h
      by_cases h31 : i = 31#5
      · subst i; small_simp
      · small_simp
    · intro i
      small_simp
    · intro a h
      simp (config := {decide := true})
        [trimPass, block, instruction, Udivti3.put, Udivti3.next, Udivti3.branch,
         state_simp_rules, spill_mem_w, apply_ite]
      apply BoolCodec.write_mem_bytes_frame
      · have := hi.stack; bv_omega
      · have := hi.stack; bv_omega
  · small_simp
  · small_simp
  · small_simp
  · small_simp

/-- Trim exits at 4452 exactly for zero, otherwise at the Small/Large comparison. -/
def TrimExit (base : BitVec 64) (count : Nat) (s : ArmState) : Prop :=
  if count = 0 then read_pc s = base + 4452#64 else
    read_pc s = base + 4372#64 ∧
    r (.GPR 8) s = BitVec.ofNat 64 (count - 1) ∧
    r (.GPR 9) s = BitVec.ofNat 64 count

/-- Arbitrarily many trailing zero bytes are removed by finite native execution. -/
theorem trim_loop (n : Nat) (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Input s data) (hp : read_pc s = base + 4328#64) (hn : n ≤ data.size)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 n)
    (h10 : r (.GPR 10) s = r (.GPR 2) s - 1#64) :
    ∃ fuel t, run fuel s = t ∧ Stable s t ∧ TrimExit base (significantBytes data n) t := by
  induction n generalizing s with
  | zero =>
    let t := block [2] s
    refine ⟨1, t, follows_run base [2] s hc he ha (by small_simp), ?_, ?_⟩
    · constructor
      · simp [t, block]
      · simp [t, block]
      · intro i h
        simp [t, block, instruction, Udivti3.branch, state_simp_rules, apply_ite]
      · intro i
        simp [t, block, instruction, Udivti3.branch, state_simp_rules, apply_ite]
      · intro a h
        simp [t, block, instruction, Udivti3.branch, state_simp_rules, apply_ite]
    · change read_pc (block [2] s) = base + 4452#64
      small_simp
  | succ n ih =>
    obtain ⟨hrun, hstable, hpc, h8', h9', h10'⟩ := trim_pass s base data hc he ha hi hp n hn h8 h10
    let t := block trimPass s
    by_cases hz : data[n]?.getD 0 = 0
    · have htpc : read_pc t = base + 4328#64 := by simpa only [if_pos hz] using hpc
      obtain ⟨fuel, u, hu, hus, hue⟩ := ih t (hstable.code hc)
        (hstable.err.trans he) (hstable.aligned ha) (hstable.input hi) htpc (by omega) h8' h10'
      refine ⟨11 + fuel, u, ?_, hstable.trans hus, ?_⟩
      · rw [run_plus, hrun, hu]
      · simpa only [significantBytes, if_pos hz] using hue
    · refine ⟨11, t, hrun, hstable, ?_⟩
      simp only [significantBytes, if_neg hz, TrimExit, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
      exact ⟨by simpa only [if_neg hz] using hpc, h8', h9'⟩

/-- One complete native packing pass: a real byte load, spill/restore, shift and OR. -/
private theorem pack_pass (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Input s data) (hp : read_pc s = base + 4392#64)
    (i count : Nat) (hic : i < count) (hc8 : count ≤ 8) (hcl : count ≤ data.size)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (8*i))
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 count)
    (h10 : r (.GPR 10) s = packPrefix data 0 i)
    (h11 : r (.GPR 11) s = BitVec.ofNat 64 i) :
    let t := block packPass s
    run 14 s = t ∧ Stable s t ∧
    read_pc t = (if i+1 = count then base + 4448#64 else base + 4392#64) ∧
    r (.GPR 8) t = BitVec.ofNat 64 (8*(i+1)) ∧
    r (.GPR 9) t = BitVec.ofNat 64 count ∧
    r (.GPR 10) t = packPrefix data 0 (i+1) ∧
    r (.GPR 11) t = BitVec.ofNat 64 (i+1) := by
  have hl := scratch_byte s data hi i (by omega)
  have hr := scratch_restore s hi.stack
  have hinc : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i+1) := by bv_omega
  have hshift := byte_shift i (by omega)
  have hpos : BitVec.ofNat 64 (8*i) + 8#64 = BitVec.ofNat 64 (8*(i+1)) := by bv_omega
  have hcmp : (AddWithCarry (BitVec.ofNat 64 count)
      (~~~BitVec.ofNat 64 (i+1)) 1#1).2.z = 1#1 ↔ i+1 = count := by
    rw [Udivti3.cmp_zero]
    bv_omega
  have hbyte : (data[i]?.getD 0).toBitVec.setWidth 64 =
      BitVec.ofNat 64 (data[i]?.getD 0).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact follows_run base packPass s hc he ha (by small_simp)
  · constructor
    · small_simp
    · small_simp
    · intro j h
      simp only [Live] at h
      by_cases h31 : j = 31#5
      · subst j; small_simp
      · small_simp
    · intro j
      small_simp
    · intro a h
      simp (config := {decide := true})
        [packPass, block, instruction, Udivti3.put, Udivti3.next, Udivti3.compare,
         Udivti3.branch, state_simp_rules, spill_mem_w, apply_ite]
      apply BoolCodec.write_mem_bytes_frame
      · have := hi.stack; bv_omega
      · have := hi.stack; bv_omega
  · by_cases hlast : i+1 = count <;> small_simp
  · small_simp
  · small_simp
  · simp only [packPrefix, Nat.zero_add]
    small_simp
    exact BitVec.or_comm _ _
  · small_simp

/-- The pack loop visits every significant byte, and never truncates the input value. -/
theorem pack_loop (remaining : Nat) (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Input s data) (i count : Nat) (hrem : i + remaining = count)
    (hc8 : count ≤ 8) (hcl : count ≤ data.size)
    (hp : read_pc s = if i = count then base + 4448#64 else base + 4392#64)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (8*i))
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 count)
    (h10 : r (.GPR 10) s = packPrefix data 0 i)
    (h11 : r (.GPR 11) s = BitVec.ofNat 64 i) :
    ∃ t, run (14*remaining) s = t ∧ Stable s t ∧ read_pc t = base + 4448#64 ∧
      r (.GPR 10) t = packPrefix data 0 count := by
  induction remaining generalizing i s with
  | zero =>
    have hic : i = count := by omega
    subst i
    exact ⟨s, rfl, Stable.refl s, by simpa using hp, h10⟩
  | succ remaining ih =>
    have hic : i < count := by omega
    have hp' : read_pc s = base + 4392#64 := by simpa only [if_neg (Nat.ne_of_lt hic)] using hp
    obtain ⟨hr, hs, hpc, h8', h9', h10', h11'⟩ :=
      pack_pass s base data hc he ha hi hp' i count hic hc8 hcl h8 h9 h10 h11
    obtain ⟨t, ht, hts, htp, htv⟩ := ih (block packPass s) (hs.code hc) (hs.err.trans he)
      (hs.aligned ha) (hs.input hi) (i+1) (by omega) hpc h8' h9' h10' h11'
    refine ⟨t, ?_, hs.trans hts, htp, htv⟩
    rw [show 14 * (remaining+1) = 14 + 14*remaining by omega, run_plus, hr, ht]

/-- Native exit contract before the parent's output stores or arena reservation.
`Stable` includes all saved registers, x0/x2/x3/x19, SIMD registers, original SP,
and a bytewise frame outside [SP-16,SP). -/
def Exit (base : BitVec 64) (data : Ssz.Bytes) (t : ArmState) : Prop :=
  let count := significantBytes data data.size
  if count ≤ 8 then
    read_pc t = base + 4460#64 ∧ r (.GPR 12) t = 0#64 ∧
      r (.GPR 10) t = packPrefix data 0 count ∧
      (r (.GPR 10) t).toNat = Ssz.readUint data 0 data.size
  else
    read_pc t = base + 4764#64 ∧ r (.GPR 8) t = BitVec.ofNat 64 (count-1) ∧
      r (.GPR 9) t = BitVec.ofNat 64 count

private theorem plain_stable (ks : List Nat) (s : ArmState)
    (hks : ks ∈ [[0, 1], [13, 14], [15, 16, 17], [32, 34], [33, 34]]) :
    Stable s (block ks s) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
  rcases hks with rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · small_simp
    · small_simp
    · intro i h
      simp only [Live] at h
      small_simp
    · intro i
      small_simp
    · intro a h
      small_simp

/-- Full finite execution of setup, unbounded zero trimming and Small packing.
No execution fact occurs in the preconditions. -/
theorem trim_and_pack (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (hp : read_pc s = base + 4320#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hi : Input s data) :
    ∃ fuel t, run fuel s = t ∧ Stable s t ∧ CodeAt t base ∧ read_err t = .None ∧
      CheckSPAlignment t ∧ Input t data ∧ Exit base data t := by
  let p := block [0, 1] s
  have hpr : run 2 s = p := follows_run base [0, 1] s hc he ha (by small_simp)
  have hps : Stable s p := plain_stable [0, 1] s (by simp)
  have hpp : read_pc p = base + 4328#64 := by dsimp [p]; small_simp
  have hp8 : r (.GPR 8) p = BitVec.ofNat 64 data.size := by
    have := hi.length
    dsimp [p]; small_simp
  have hp10 : r (.GPR 10) p = r (.GPR 2) p - 1#64 := by dsimp [p]; small_simp
  obtain ⟨nf, u, hur, hus, hue⟩ := trim_loop data.size p base data
    (hps.code hc) (hps.err.trans he) (hps.aligned ha) (hps.input hi) hpp
    (Nat.le_refl _) hp8 hp10
  have hsu := hps.trans hus
  have hrunu : run (2+nf) s = u := by rw [run_plus, hpr, hur]
  let count := significantBytes data data.size
  change TrimExit base count u at hue
  have hcl : count ≤ data.size := significantBytes_le data data.size
  have huc := hsu.code hc
  have hue' := hsu.err.trans he
  have hua := hsu.aligned ha
  have hui := hsu.input hi
  have finish : ∀ fuel t, run fuel u = t → Stable u t → Exit base data t →
      ∃ fuel t, run fuel s = t ∧ Stable s t ∧ CodeAt t base ∧ read_err t = .None ∧
        CheckSPAlignment t ∧ Input t data ∧ Exit base data t := by
    intro fuel t hr hs hx
    have hst := hsu.trans hs
    refine ⟨2+nf+fuel, t, ?_, hst, hst.code hc, hst.err.trans he,
      hst.aligned ha, hst.input hi, hx⟩
    rw [run_plus, hrunu, hr]
  by_cases hz : count = 0
  · have hup : read_pc u = base + 4452#64 := by simpa only [TrimExit, if_pos hz] using hue
    let t := block [33, 34] u
    have hr : run 2 u = t := follows_run base [33, 34] u huc hue' hua (by small_simp)
    apply finish 2 t hr (plain_stable [33, 34] u (by simp))
    have hv := readUint_significantBytes data data.size
    simp only [show significantBytes data data.size = 0 from hz, Ssz.readUint] at hv
    change r .PC u = base + 4452#64 at hup
    simp (config := {decide := true, instances := true})
      [Exit, show significantBytes data data.size = 0 from hz,
       t, block, instruction, Udivti3.put, Udivti3.next, state_simp_rules,
       hup, BitVec.add_assoc, packPrefix, ← hv]
  · have hut : read_pc u = base + 4372#64 ∧
        r (.GPR 8) u = BitVec.ofNat 64 (count-1) ∧
        r (.GPR 9) u = BitVec.ofNat 64 count := by
      simpa only [TrimExit, if_neg hz] using hue
    let v := block [13, 14] u
    have hvr : run 2 u = v := follows_run base [13, 14] u huc hue' hua (by
      have := hut.1; small_simp)
    have hvs : Stable u v := plain_stable [13, 14] u (by simp)
    have hcmp : (AddWithCarry (BitVec.ofNat 64 count) (~~~9#64) 1#1).2.c = 1#1 ↔ 9 ≤ count := by
      rw [Udivti3.cmp_carry]
      have := hi.bounded
      bv_omega
    have hvp : read_pc v = if 9 ≤ count then base + 4764#64 else base + 4380#64 := by
      have := hut.1; have := hut.2.2
      dsimp [v]; small_simp
    have hv9 : r (.GPR 9) v = BitVec.ofNat 64 count := by
      have := hut.2.2; dsimp [v]; small_simp
    by_cases hsmall : count ≤ 8
    · have hvp' : read_pc v = base + 4380#64 := by simpa only [if_neg (by omega : ¬9 ≤ count)] using hvp
      let w := block [15, 16, 17] v
      have hws : Stable v w := plain_stable [15, 16, 17] v (by simp)
      have hwr : run 3 v = w := follows_run base [15, 16, 17] v (hvs.code huc)
        (hvs.err.trans hue') (hvs.aligned hua) (by small_simp)
      have hwp : read_pc w = if 0 = count then base + 4448#64 else base + 4392#64 := by
        have hnon : ¬0 = count := Ne.symm hz
        dsimp [w]; small_simp
      have hw8 : r (.GPR 8) w = BitVec.ofNat 64 (8*0) := by dsimp [w]; small_simp
      have hw9 : r (.GPR 9) w = BitVec.ofNat 64 count := by dsimp [w]; small_simp
      have hw10 : r (.GPR 10) w = packPrefix data 0 0 := by dsimp [w]; simp only [packPrefix]; small_simp
      have hw11 : r (.GPR 11) w = BitVec.ofNat 64 0 := by dsimp [w]; small_simp
      have husw := hvs.trans hws
      obtain ⟨z, hzr, hzs, hzp, hzv⟩ := pack_loop count w base data
        (husw.code huc) (husw.err.trans hue') (husw.aligned hua) (husw.input hui)
        0 count (by omega) hsmall hcl hwp hw8 hw9 hw10 hw11
      let t := block [32, 34] z
      have hsz := husw.trans hzs
      have htr : run 2 z = t := follows_run base [32, 34] z (hsz.code huc)
        (hsz.err.trans hue') (hsz.aligned hua) (by small_simp)
      have hts := plain_stable [32, 34] z (by simp)
      apply finish (2+3+14*count+2) t
      · rw [run_plus, run_plus, run_plus, hvr, hwr, hzr, htr]
      · exact hsz.trans hts
      · have hv : (packPrefix data 0 count).toNat = Ssz.readUint data 0 data.size :=
          (packPrefix_toNat data 0 count hsmall).trans (readUint_significantBytes data data.size)
        simp only [Exit, show significantBytes data data.size = count from rfl, if_pos hsmall]
        dsimp [t]
        small_simp
    · apply finish 2 v hvr hvs
      have hlarge : 9 ≤ count := by omega
      have hv8 : r (.GPR 8) v = BitVec.ofNat 64 (count-1) := by
        have := hut.2.1; dsimp [v]; small_simp
      simp only [Exit, show significantBytes data data.size = count from rfl, if_neg hsmall]
      exact ⟨by simpa only [if_pos hlarge] using hvp, hv8, hv9⟩

end SszArm.UintCodec.Small
