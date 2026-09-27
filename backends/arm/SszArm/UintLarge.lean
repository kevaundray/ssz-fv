import SszArm.UintLimbMemory

namespace SszArm.UintCodec.Large

open SszNative.WordDecode

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def setupPass : List Nat := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
private def bytePass : List Nat := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
private def storePass : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

private theorem read_two_spills_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (address first second : BitVec 64) (a b : BitVec 64) :
    read_mem_bytes n address
      (write_mem_bytes 8 second b (write_mem_bytes 8 first a (w f v s))) =
    read_mem_bytes n address
      (write_mem_bytes 8 second b (write_mem_bytes 8 first a s)) := by
  exact (Memory.mem_eq_iff_read_mem_bytes_eq.mp
    (mem_write_mem_bytes_of_mem_eq (spill_mem_w s f v 8 first a) 8 second b)) n address

macro "limb_simp" : tactic => `(tactic|
  simp_all (config := {decide := true, instances := true})
    [setupPass, bytePass, storePass, Follows, block, instruction, subtract,
     Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
     state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel,
     read_spill_w, read_two_spills_w, apply_ite])

private theorem byte_shift (i : Nat) (hi : i < 8) :
    (BitVec.ofInt 6 ((BitVec.ofNat 64 (8*i)).toInt % 64)).toNat = 8*i := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem quiet_input {s t : ArmState} {data : Ssz.Bytes}
    (h : Stable 0 0 s t) (hi : Small.Input s data) : Small.Input t data := by
  have h2 := h.regs 2 (by decide)
  have h3 := h.regs 3 (by decide)
  have h31 := h.regs 31 (by decide)
  refine ⟨h3.trans hi.length, hi.bounded, ?_, ?_, ?_, ?_⟩
  · simpa only [h2] using hi.range
  · simpa only [h31] using hi.stack
  · simpa only [h2, h31] using hi.separated
  · intro i hin
    rw [h2, BoolCodec.read_one]
    change t.mem (r (.GPR 2) s + BitVec.ofNat 64 i) = _
    rw [h.frame _ (Or.inr (Nat.zero_le _))
      (by have := hi.range; have := hi.separated; bv_omega)]
    simpa only [BoolCodec.read_one, read_mem, read_store] using hi.bytes i hin

private structure InnerStable (s t : ArmState) : Prop extends Stable 0 0 s t where
  offset : r (.GPR 13) t = r (.GPR 13) s
  index : r (.GPR 14) t = r (.GPR 14) s
  remaining : r (.GPR 16) t = r (.GPR 16) s

private theorem InnerStable.refl (s : ArmState) : InnerStable s s :=
  ⟨Stable.refl 0 0 s, rfl, rfl, rfl⟩

private theorem InnerStable.trans {s t u : ArmState}
    (h : InnerStable s t) (g : InnerStable t u) : InnerStable s u :=
  ⟨h.toStable.trans g.toStable, g.offset.trans h.offset,
    g.index.trans h.index, g.remaining.trans h.remaining⟩

private theorem plain_stable (ks : List Nat) (s : ArmState)
    (hks : ks = setupPass ∨ ks = [38]) : Stable 0 0 s (block ks s) := by
  rcases hks with rfl | rfl
  all_goals
    constructor
    · limb_simp
    · limb_simp
    · intro i hi; simp only [Live] at hi; limb_simp
    · intro i; limb_simp
    · intro a hd hs; limb_simp

/-- The outer header computes min(remaining,8) and saturating accessible bytes.
Since this is a live limb, its zero-count bypass is impossible. -/
private theorem setup_pass (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Small.Input s data) (hp : read_pc s = base + 6920#64)
    (count index n : Nat) (hn : 0 < n) (hcount : 8*index+n = count)
    (hcl : count ≤ data.size)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 n)
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 count)
    (h13 : r (.GPR 13) s = BitVec.ofNat 64 (8*index))
    (h14 : r (.GPR 14) s = BitVec.ofNat 64 index)
    (h15 : r (.GPR 15) s = 8#64) :
    let t := block setupPass s
    run 10 s = t ∧ Stable 0 0 s t ∧ read_pc t = base + 6960#64 ∧
    r (.GPR 1) t = packPrefix data (8*index) 0 ∧
    r (.GPR 4) t = 0#64 ∧ r (.GPR 8) t = BitVec.ofNat 64 (8*index) ∧
    r (.GPR 13) t = BitVec.ofNat 64 (8*index) ∧
    r (.GPR 14) t = BitVec.ofNat 64 index ∧
    r (.GPR 16) t = BitVec.ofNat 64 n - 8#64 ∧
    r (.GPR 17) t = BitVec.ofNat 64 (min n 8) ∧
    r (.GPR 18) t = BitVec.ofNat 64 (data.size - 8*index) := by
  have hb := hi.bounded
  have hlen := hi.length
  have hshift : BitVec.ofNat 64 index <<< 3 = BitVec.ofNat 64 (8*index) := by bv_omega
  have hneq : BitVec.ofNat 64 count ≠ BitVec.ofNat 64 (8*index) := by bv_omega
  have hcmp : (AddWithCarry (BitVec.ofNat 64 count)
      (~~~BitVec.ofNat 64 (8*index)) 1#1).2.z ≠ 1#1 := by
    simpa only [ne_eq, Udivti3.cmp_zero] using hneq
  have hcarry : (AddWithCarry (BitVec.ofNat 64 data.size)
      (~~~BitVec.ofNat 64 (8*index)) 1#1).2.c = 1#1 := by
    rw [Udivti3.cmp_carry]; bv_omega
  have hsub : BitVec.ofNat 64 data.size - BitVec.ofNat 64 (8*index) =
      BitVec.ofNat 64 (data.size - 8*index) := by bv_omega
  have hcarry8 : (AddWithCarry (BitVec.ofNat 64 n) (~~~8#64) 1#1).2.c = 1#1 ↔ 8 ≤ n := by
    rw [Udivti3.cmp_carry]
    bv_omega
  dsimp only
  refine ⟨follows_run base setupPass s hc he ha (by limb_simp),
    plain_stable setupPass s (Or.inl rfl), ?_⟩
  simp only [packPrefix]
  by_cases hn8 : n < 8
  · have hsmall : n ≤ 8 := by omega
    simp_all (config := {decide := true, instances := true})
      [setupPass, block, instruction, subtract,
       Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
       state_simp_rules, BitVec.add_assoc, Nat.min_eq_left hsmall]
  · have hlarge : 8 ≤ n := by omega
    simp_all (config := {decide := true, instances := true})
      [setupPass, block, instruction, subtract,
       Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
       state_simp_rules, BitVec.add_assoc, Nat.min_eq_right hlarge]

/-- One native byte iteration, including the nonzero accessibility check and
x9/SP spill restoration. The panic branch at 6960 is never taken. -/
private theorem byte_pass (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Small.Input s data) (hp : read_pc s = base + 6960#64)
    (start i chunk : Nat) (hic : i < chunk) (hc8 : chunk ≤ 8)
    (hcl : start+chunk ≤ data.size)
    (h1 : r (.GPR 1) s = packPrefix data start i)
    (h4 : r (.GPR 4) s = BitVec.ofNat 64 (8*i))
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (start+i))
    (h17 : r (.GPR 17) s = BitVec.ofNat 64 (chunk-i))
    (h18 : r (.GPR 18) s = BitVec.ofNat 64 (data.size-(start+i))) :
    let t := block bytePass s
    run 15 s = t ∧ InnerStable s t ∧
    read_pc t = (if i+1 = chunk then base + 7020#64 else base + 6960#64) ∧
    r (.GPR 1) t = packPrefix data start (i+1) ∧
    r (.GPR 4) t = BitVec.ofNat 64 (8*(i+1)) ∧
    r (.GPR 8) t = BitVec.ofNat 64 (start+(i+1)) ∧
    r (.GPR 17) t = BitVec.ofNat 64 (chunk-(i+1)) ∧
    r (.GPR 18) t = BitVec.ofNat 64 (data.size-(start+(i+1))) := by
  have hb := hi.bounded
  have hl := Small.scratch_byte s data hi (start+i) (by omega)
  have hr := Small.scratch_restore s hi.stack
  have hpanic : BitVec.ofNat 64 (data.size-(start+i)) ≠ 0#64 := by bv_omega
  have hshift := byte_shift i (by omega)
  have hdec17 : BitVec.ofNat 64 (chunk-i) - 1#64 = BitVec.ofNat 64 (chunk-(i+1)) := by bv_omega
  have hdec18 : BitVec.ofNat 64 (data.size-(start+i)) - 1#64 =
      BitVec.ofNat 64 (data.size-(start+(i+1))) := by bv_omega
  have hinc : BitVec.ofNat 64 (start+i) + 1#64 = BitVec.ofNat 64 (start+(i+1)) := by bv_omega
  have hpos : BitVec.ofNat 64 (8*i) + 8#64 = BitVec.ofNat 64 (8*(i+1)) := by bv_omega
  have hend : BitVec.ofNat 64 (chunk-(i+1)) = 0#64 ↔ i+1 = chunk := by bv_omega
  have hbyte : (data[start+i]?.getD 0).toBitVec.setWidth 64 =
      BitVec.ofNat 64 (data[start+i]?.getD 0).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
  dsimp only
  refine ⟨follows_run base bytePass s hc he ha (by limb_simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · constructor
      · limb_simp
      · limb_simp
      · intro j hj
        simp only [Live] at hj
        by_cases h31 : j = 31#5
        · subst j; limb_simp
        · by_cases h9 : j = 9#5
          · subst j; limb_simp
          · limb_simp
      · intro j; limb_simp
      · intro a hd hs
        simp (config := {decide := true})
          [bytePass, block, instruction, Udivti3.put, Udivti3.next,
           Udivti3.branch, state_simp_rules, spill_mem_w, apply_ite]
        apply BoolCodec.write_mem_bytes_frame
        · have := hi.stack; bv_omega
        · have := hi.stack; bv_omega
    · limb_simp
    · limb_simp
    · limb_simp
  · by_cases hlast : i+1 = chunk <;> limb_simp
  · simp only [packPrefix]
    limb_simp
    exact BitVec.or_comm _ _
  · limb_simp
  · limb_simp
  · limb_simp
  · limb_simp

private theorem byte_loop (remaining : Nat) (s : ArmState) (base : BitVec 64)
    (data : Ssz.Bytes) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hi : Small.Input s data)
    (start i chunk : Nat) (hrem : i+remaining = chunk) (hc8 : chunk ≤ 8)
    (hcl : start+chunk ≤ data.size)
    (hp : read_pc s = if i = chunk then base + 7020#64 else base + 6960#64)
    (h1 : r (.GPR 1) s = packPrefix data start i)
    (h4 : r (.GPR 4) s = BitVec.ofNat 64 (8*i))
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (start+i))
    (h17 : r (.GPR 17) s = BitVec.ofNat 64 (chunk-i))
    (h18 : r (.GPR 18) s = BitVec.ofNat 64 (data.size-(start+i))) :
    ∃ t, run (15*remaining) s = t ∧ InnerStable s t ∧
      read_pc t = base + 7020#64 ∧ r (.GPR 1) t = packPrefix data start chunk := by
  induction remaining generalizing i s with
  | zero =>
    have hic : i = chunk := by omega
    subst i
    exact ⟨s, rfl, InnerStable.refl s, by simpa using hp, h1⟩
  | succ remaining ih =>
    have hic : i < chunk := by omega
    have hpc : read_pc s = base + 6960#64 := by
      simpa only [if_neg (Nat.ne_of_lt hic)] using hp
    obtain ⟨hr, hs, hp', h1', h4', h8', h17', h18'⟩ :=
      byte_pass s base data hc he ha hi hpc start i chunk hic hc8 hcl h1 h4 h8 h17 h18
    obtain ⟨t, ht, hts, htp, htv⟩ := ih (block bytePass s)
      (hs.toStable.code hc) (hs.toStable.err.trans he) (hs.toStable.aligned ha)
      (quiet_input hs.toStable hi) (i+1) (by omega) hp' h1' h4' h8' h17' h18'
    refine ⟨t, ?_, hs.trans hts, htp, htv⟩
    rw [show 15*(remaining+1) = 15+15*remaining by omega, run_plus, hr, ht]

/-- The real STR writes a full 64-bit word. It does not touch arena metadata;
the spilled count is restored even though the destination store intervenes. -/
private theorem store_pass (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (pointer : BitVec 64) (count index n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (ar : Area s data pointer count) (hp : read_pc s = base + 6868#64)
    (hn : 0 < n) (hcount : 8*index+n = count) (hcl : count ≤ data.size)
    (h11 : r (.GPR 11) s = BitVec.ofNat 64 ((count+7)/8-1))
    (h12 : r (.GPR 12) s = pointer)
    (h13 : r (.GPR 13) s = BitVec.ofNat 64 (8*index))
    (h14 : r (.GPR 14) s = BitVec.ofNat 64 index)
    (h16 : r (.GPR 16) s = BitVec.ofNat 64 n - 8#64) :
    let t := block storePass s
    run 13 s = t ∧ Stable (pointer.toNat+8*index) (pointer.toNat+8*((count+7)/8)) s t ∧
    read_pc t = (if n ≤ 8 then base + 4460#64 else base + 6920#64) ∧
    read_mem_bytes 8 (BitVec.ofNat 64 (pointer.toNat+8*index)) t = r (.GPR 1) s ∧
    r (.GPR 8) t = BitVec.ofNat 64 n - 8#64 ∧
    r (.GPR 13) t = BitVec.ofNat 64 (8*(index+1)) ∧
    r (.GPR 14) t = BitVec.ofNat 64 (index+1) := by
  have hb := ar.input.bounded
  have hspace := ar.range
  have hstack := ar.input.stack
  have hsep := ar.scratch
  have hindex : index < (count+7)/8 := by omega
  have hshift : BitVec.ofNat 64 index <<< 3 = BitVec.ofNat 64 (8*index) := by bv_omega
  have haddr : pointer + BitVec.ofNat 64 (8*index) =
      BitVec.ofNat 64 (pointer.toNat+8*index) := by bv_omega
  have hdspace : (BitVec.ofNat 64 (pointer.toNat+8*index)).toNat+8 ≤ 2^64 := by bv_omega
  have hrestore : read_mem_bytes 8 (r (.GPR 31) s - 16#64)
      (write_mem_bytes 8 (BitVec.ofNat 64 (pointer.toNat+8*index)) (r (.GPR 1) s)
        (write_mem_bytes 8 (r (.GPR 31) s - 16#64) (r (.GPR 9) s) s)) = r (.GPR 9) s := by
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
    · exact Small.scratch_restore s hstack
    · bv_omega
    · exact hdspace
    · bv_omega
  have hstored := BoolCodec.read_mem_bytes_write_mem_bytes_same
    (write_mem_bytes 8 (r (.GPR 31) s - 16#64) (r (.GPR 9) s) s)
    8 (BitVec.ofNat 64 (pointer.toNat+8*index)) (r (.GPR 1) s) hdspace
  have hlast : (AddWithCarry (BitVec.ofNat 64 index)
      (~~~BitVec.ofNat 64 ((count+7)/8-1)) 1#1).2.z = 1#1 ↔ n ≤ 8 := by
    rw [Udivti3.cmp_zero]; bv_omega
  have hinc : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index+1) := by bv_omega
  have hoff : BitVec.ofNat 64 (8*index) + 8#64 = BitVec.ofNat 64 (8*(index+1)) := by bv_omega
  dsimp only
  refine ⟨follows_run base storePass s hc he ha (by limb_simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · limb_simp
    · limb_simp
    · intro j hj
      simp only [Live] at hj
      by_cases h31 : j = 31#5
      · subst j; limb_simp
      · by_cases h9 : j = 9#5
        · subst j; limb_simp
        · limb_simp
    · intro j; limb_simp
    · intro a hd hs
      simp (config := {decide := true}) only
        [storePass, block, instruction, Udivti3.put, Udivti3.next,
         Udivti3.compare, Udivti3.branch, state_simp_rules,
         spill_mem_w, apply_ite, h12, h14, hshift, haddr]
      rw [BoolCodec.write_mem_bytes_frame _ _ _ _ _ hdspace (by bv_omega)]
      simp only [spill_mem_w]
      apply BoolCodec.write_mem_bytes_frame <;> bv_omega
  · by_cases hsmall : n ≤ 8 <;> limb_simp
  · limb_simp
  · limb_simp
  · limb_simp
  · limb_simp

/-- Induction on remaining bytes proves both native loops finite. The destination
suffix frame lets the recursive run retain the word just stored. -/
private theorem outer_loop (n : Nat) (s : ArmState) (base : BitVec 64)
    (data : Ssz.Bytes) (pointer : BitVec 64) (count index : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (ar : Area s data pointer count) (hp : read_pc s = base + 6920#64)
    (hn : 0 < n) (hcount : 8*index+n = count) (hcl : count ≤ data.size)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 n)
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 count)
    (h11 : r (.GPR 11) s = BitVec.ofNat 64 ((count+7)/8-1))
    (h12 : r (.GPR 12) s = pointer)
    (h13 : r (.GPR 13) s = BitVec.ofNat 64 (8*index))
    (h14 : r (.GPR 14) s = BitVec.ofNat 64 index)
    (h15 : r (.GPR 15) s = 8#64) :
    ∃ fuel t, run fuel s = t ∧
      Stable (pointer.toNat+8*index) (pointer.toNat+8*((count+7)/8)) s t ∧
      read_pc t = base + 4460#64 ∧
      Stored t (pointer.toNat+8*index) (decodeWords data (8*index) n) := by
  induction n using Nat.strongRecOn generalizing s index with
  | ind n ih =>
    obtain ⟨hur, hus, hup, hu1, hu4, hu8, hu13, hu14, hu16, hu17, hu18⟩ :=
      setup_pass s base data hc he ha ar.input hp count index n hn hcount hcl
        h8 h9 h13 h14 h15
    let u := block setupPass s
    have hchunk : 0 < min n 8 := by omega
    obtain ⟨v, hvr, hvs, hvp, hv1⟩ := byte_loop (min n 8) u base data
      (hus.code hc) (hus.err.trans he) (hus.aligned ha) (quiet_input hus ar.input)
      (8*index) 0 (min n 8) (by omega) (by omega) (by omega)
      (by simpa only [if_neg (Ne.symm (Nat.ne_of_gt hchunk))] using hup)
      hu1 (by simpa using hu4) (by simpa using hu8)
      (by simpa using hu17) (by simpa using hu18)
    let w := block [38] v
    have hwr : run 1 v = w := follows_run base [38] v
      (hvs.toStable.code (hus.code hc)) (hvs.toStable.err.trans (hus.err.trans he))
      (hvs.toStable.aligned (hus.aligned ha))
      (by exact ⟨by decide, hvp, trivial⟩)
    have hws : Stable 0 0 v w := plain_stable [38] v (Or.inr rfl)
    have hsw := hus.trans (hvs.toStable.trans hws)
    have hwp : read_pc w = base + 6868#64 := by
      have hpc : r .PC v = base + 7020#64 := hvp
      simp (config := {decide := true, instances := true})
        [w, block, instruction, state_simp_rules, hpc, BitVec.sub_eq_add_neg,
         BitVec.add_assoc]
    have hw1 : r (.GPR 1) w = packPrefix data (8*index) (min n 8) := by
      simpa (config := {decide := true, instances := true}) only
        [w, block, instruction, state_simp_rules, BitVec.ofNat_eq_ofNat] using hv1
    have hw13 : r (.GPR 13) w = BitVec.ofNat 64 (8*index) := by
      simpa (config := {decide := true, instances := true}) only
        [w, block, instruction, state_simp_rules, BitVec.ofNat_eq_ofNat] using hvs.offset.trans hu13
    have hw14 : r (.GPR 14) w = BitVec.ofNat 64 index := by
      simpa (config := {decide := true, instances := true}) only
        [w, block, instruction, state_simp_rules, BitVec.ofNat_eq_ofNat] using hvs.index.trans hu14
    have hw16 : r (.GPR 16) w = BitVec.ofNat 64 n - 8#64 := by
      simpa (config := {decide := true, instances := true}) only
        [w, block, instruction, state_simp_rules, BitVec.ofNat_eq_ofNat] using hvs.remaining.trans hu16
    let lo := pointer.toNat+8*index
    let hi := pointer.toNat+8*((count+7)/8)
    have hsw' : Stable lo hi s w := hsw.allow lo hi
    have aw : Area w data pointer count := hsw'.area ar (by dsimp [lo]; omega) (Nat.le_refl _)
    obtain ⟨htr, hts, htp, htm, ht8, ht13, ht14⟩ :=
      store_pass w base data pointer count index n (hsw.code hc)
        (hsw.err.trans he) (hsw.aligned ha) aw hwp hn hcount hcl
        ((hsw.regs 11 (by decide)).trans h11)
        ((hsw.regs 12 (by decide)).trans h12) hw13 hw14 hw16
    let t := block storePass w
    have hst : Stable lo hi s t := hsw'.trans hts
    have atr : Area t data pointer count := hst.area ar (by dsimp [lo]; omega) (Nat.le_refl _)
    have hrun : run (10+15*min n 8+1+13) s = t := by
      rw [run_plus, run_plus, run_plus, hur, hvr, hwr, htr]
    have hword : read_mem_bytes 8 (BitVec.ofNat 64 lo) t =
        packPrefix data (8*index) (min n 8) := htm.trans hw1
    by_cases hsmall : n ≤ 8
    · refine ⟨10+15*min n 8+1+13, t, hrun, hst, ?_, ?_⟩
      · simpa only [if_pos hsmall] using htp
      · rw [decodeWords, if_neg (Nat.ne_of_gt hn)]
        dsimp only
        simp only [Nat.min_eq_left hsmall, Nat.sub_self]
        rw [decodeWords]
        exact ⟨by simpa only [lo, Nat.min_eq_left hsmall] using hword, trivial⟩
    · have hlarge : 8 < n := by omega
      have htpc : read_pc t = base + 6920#64 := by simpa only [if_neg hsmall] using htp
      have ht8' : r (.GPR 8) t = BitVec.ofNat 64 (n-8) := by
        rw [ht8]; have := ar.input.bounded; bv_omega
      obtain ⟨fuel, z, hzr, hzs, hzp, hzm⟩ := ih (n-8) (by omega) t (index+1)
        (hst.code hc) (hst.err.trans he) (hst.aligned ha) atr htpc (by omega)
        (by omega) ht8' ((hst.regs 9 (by decide)).trans h9)
        ((hst.regs 11 (by decide)).trans h11) ((hst.regs 12 (by decide)).trans h12)
        ht13 ht14 ((hst.regs 15 (by decide)).trans h15)
      have hzs' : Stable lo hi t z := hzs.enlarge (by dsimp [lo]; omega) (Nat.le_refl _)
      refine ⟨10+15*min n 8+1+13+fuel, z, ?_, hst.trans hzs', hzp, ?_⟩
      · rw [run_plus, hrun, hzr]
      · rw [decodeWords, if_neg (Nat.ne_of_gt hn), Nat.min_eq_right (by omega : 8 ≤ n)]
        constructor
        · have hh := hzs.read lo 8 (by have := ar.range; dsimp [lo]; omega)
            (Or.inl (by dsimp [lo]; omega))
            (by
              have hsep := atr.scratch
              simp only [BitVec.ofNat_eq_ofNat] at hsep ⊢
              dsimp only [lo]
              omega)
          exact hh.trans (by simpa only [Nat.min_eq_right (by omega : 8 ≤ n)] using hword)
        · simpa only [lo, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hzm

/-- Complete actual execution from the committed allocation to the Nat output
tail. The final short-word subtraction is deliberately kept as modular SUB;
its wrapped value is dead when the last-word comparison exits. -/
theorem fill (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (pointer : BitVec 64) (count : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (ar : Area s data pointer count) (hp : read_pc s = base + 6920#64)
    (hn : 9 ≤ count) (hcl : count ≤ data.size)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 count)
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 count)
    (h10 : r (.GPR 10) s = BitVec.ofNat 64 ((count+7)/8))
    (h11 : r (.GPR 11) s = BitVec.ofNat 64 ((count+7)/8-1))
    (h12 : r (.GPR 12) s = pointer)
    (h13 : r (.GPR 13) s = 0#64) (h14 : r (.GPR 14) s = 0#64)
    (h15 : r (.GPR 15) s = 8#64) :
    ∃ fuel t, run fuel s = t ∧
      Stable pointer.toNat (pointer.toNat+8*((count+7)/8)) s t ∧
      CodeAt t base ∧ read_err t = .None ∧ CheckSPAlignment t ∧
      Area t data pointer count ∧ read_pc t = base + 4460#64 ∧
      r (.GPR 12) t = pointer ∧ r (.GPR 10) t = BitVec.ofNat 64 ((count+7)/8) ∧
      (r (.GPR 10) t).toNat = (decodeWords data 0 count).length ∧
      SszNative.NatMemory.wordsAt (widthLoad t) pointer.toNat (decodeWords data 0 count) ∧
      SszNative.Limbs.value (decodeWords data 0 count) = Ssz.readUint data 0 count := by
  obtain ⟨fuel, t, hr, hs, hpc, hm⟩ := outer_loop count s base data pointer count 0
    hc he ha ar hp (by omega) (by omega) hcl h8 h9 h11 h12 h13 h14 h15
  simp only [Nat.mul_zero, Nat.add_zero] at hs hm
  have ht10 := (hs.regs 10 (by decide)).trans h10
  refine ⟨fuel, t, hr, hs, hs.code hc, hs.err.trans he, hs.aligned ha,
    hs.area ar (Nat.le_refl _) (Nat.le_refl _), hpc,
    (hs.regs 12 (by decide)).trans h12, ht10, ?_, hm.wordsAt, decodeWords_value data 0 count⟩
  rw [ht10, decodeWords_length]
  have := ar.input.bounded
  bv_omega

end SszArm.UintCodec.Large
