import SszArm.UintPrepareProofs
import SszArm.UintReservation

namespace SszArm.UintCodec

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

private theorem prepareBlock_program (ks : List Nat) (s : ArmState) :
    (prepareBlock ks s).program = s.program := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => exact (ih (prepareInstruction k s)).trans (prepareInstruction_program k s)

theorem prepare_correct (s : ArmState) (base : BitVec 64) (count : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 4764#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hsp : 16 ≤ (r (.GPR 31#5) s).toNat) (hpos : 0 < count) (hcount : count < 2^63)
    (h8 : (r (.GPR 8#5) s).toNat = count - 1) :
    let t := run 10 s
    read_pc t = (if 8 * SszNative.Arena.wordsForBytes count < 2^63
      then base + 6776#64 else base + 4816#64) ∧
    (r (.GPR 10#5) t).toNat = SszNative.Arena.wordsForBytes count ∧
    (r (.GPR 13#5) t).toNat = 8 * SszNative.Arena.wordsForBytes count ∧
    t.mem = (prepareSpill s).mem ∧ CodeAt t base ∧ read_err t = .None ∧
    CheckSPAlignment t ∧ ∀ f, PreparePreserved f → r f t = r f s := by
  dsimp only
  rw [prepare_runs s base hc hp he ha]
  have hx := prepare_trace_effect s base hp hsp
  have hw := prepared_word_count s count hpos hcount h8
  have hb := prepared_byte_count s count hpos hcount h8
  have hf := prepare_trace_field s
  have hregs := fun f h => hf f h hsp
  refine ⟨?_, ?_, ?_, hx.2.2.2.2, ?_, ?_, ?_, hregs⟩
  · simpa only [hb] using hx.1
  · rw [hx.2.2.1]; exact hw
  · rw [hx.2.2.2.1]; exact hb
  · intro row hr
    simpa only [prepareBlock_program] using hc row hr
  · exact (hregs .ERR (by trivial)).trans he
  · have h := hregs (.GPR 31#5) (by decide)
    simpa only [CheckSPAlignment, state_simp_rules, h] using ha

/-- The descriptor arena header is not part of the lowering spill. -/
def ArenaOutsideSpill (s : ArmState) : Prop :=
  (r (.GPR 19#5) s).toNat + 24 ≤ 2^64 ∧
  ((r (.GPR 19#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 19#5) s).toNat)

theorem prepare_header (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 4764#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hsp : 16 ≤ (r (.GPR 31#5) s).toNat) (hh : ArenaOutsideSpill s)
    (offset : Nat) (hoff : offset ≤ 16) :
    read_mem_bytes 8 (r (.GPR 19#5) (run 10 s) + BitVec.ofNat 64 offset) (run 10 s) =
      read_mem_bytes 8 (r (.GPR 19#5) s + BitVec.ofNat 64 offset) s := by
  rw [prepare_runs s base hc hp he ha]
  rw [prepare_trace_field s (.GPR 19#5) (by decide) hsp]
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp
    (prepare_trace_effect s base hp hsp).2.2.2.2) 8]
  unfold prepareSpill
  obtain ⟨hspace, hsep⟩ := hh
  apply BoolCodec.read_mem_bytes_write_mem_bytes_disjoint <;> bv_omega

def AllocationResult (s t : ArmState) (base : BitVec 64) (count : Nat) : Prop :=
  (r (.GPR 10) t).toNat = SszNative.Arena.wordsForBytes count ∧
  CodeAt t base ∧ read_err t = .None ∧
  (match SszNative.Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat
      (arenaUsed s).toNat (SszNative.Arena.wordsForBytes count) with
   | none => read_pc t = base + 4816#64 ∧ t.mem = (prepareSpill s).mem
   | some reservation =>
     read_pc t = base + 6920#64 ∧ (r (.GPR 12) t).toNat = reservation.pointer ∧
     (r (.GPR 16) t).toNat = reservation.used ∧
     t.mem = (write_mem_bytes 8 (r (.GPR 19) s + 16#64)
       (BitVec.ofNat 64 reservation.used) (prepareSpill s)).mem ∧
     r (.GPR 8) t = r (.GPR 8) s + 1#64 ∧ r (.GPR 13) t = 0#64 ∧
     r (.GPR 14) t = 0#64 ∧ r (.GPR 15) t = 8#64) ∧
  (r (.GPR 11) t).toNat = SszNative.Arena.wordsForBytes count - 1 ∧
  ∀ f, PreparePreserved f → ArenaPreserved f → r f t = r f s

/-- The complete size check and reservation path, including early isize
rejection, refines the same pure reservation on the original arena header. -/
theorem allocation_runs (s : ArmState) (base : BitVec 64) (count : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 4764#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hsp : 16 ≤ (r (.GPR 31#5) s).toNat) (hh : ArenaOutsideSpill s)
    (hpos : 0 < count) (hcount : count < 2^63)
    (h8 : (r (.GPR 8#5) s).toNat = count - 1) :
    ∃ fuel, AllocationResult s (run fuel s) base count := by
  let u := run 10 s
  let words := SszNative.Arena.wordsForBytes count
  obtain ⟨hpp, hw, hb, hm, huc, hue, hua, huf⟩ :=
    prepare_correct s base count hc hp he ha hsp hpos hcount h8
  change read_pc u = (if 8 * words < 2^63 then base + 6776#64 else base + 4816#64) at hpp
  have positive : 0 < words := by
    dsimp [words, SszNative.Arena.wordsForBytes]
    simp [show count ≠ 0 by omega]
    omega
  have hlast : (r (.GPR 11) u).toNat = words - 1 := by
    change (r (.GPR 11#5) (run 10 s)).toNat = words - 1
    rw [prepare_runs s base hc hp he ha, (prepare_trace_effect s base hp hsp).2.1]
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h8, words,
      SszNative.Arena.wordsForBytes, Nat.ne_of_gt hpos]
  have hbase : arenaBase u = arenaBase s := by
    change read_mem_bytes 8 (r (.GPR 19#5) u) u =
      read_mem_bytes 8 (r (.GPR 19#5) s) s
    have hz := prepare_header s base hc hp he ha hsp hh 0 (by omega)
    change read_mem_bytes 8 (r (.GPR 19#5) u + 0#64) u =
      read_mem_bytes 8 (r (.GPR 19#5) s + 0#64) s at hz
    simpa only [BitVec.add_zero] using hz
  have hcap : arenaCapacity u = arenaCapacity s :=
    prepare_header s base hc hp he ha hsp hh 8 (by omega)
  have hused : arenaUsed u = arenaUsed s :=
    prepare_header s base hc hp he ha hsp hh 16 (by omega)
  have hr : SszNative.Arena.reserve (arenaBase u).toNat (arenaCapacity u).toNat
      (arenaUsed u).toNat words =
      SszNative.Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat
        (arenaUsed s).toNat words := by rw [hbase, hcap, hused]
  by_cases hi : 8 * words < 2^63
  · have hpu : read_pc u = base + 6776#64 := by
      simpa only [hi, ↓reduceIte] using hpp
    cases hs : SszNative.Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat
        (arenaUsed s).toNat words with
    | none =>
      obtain ⟨hpc, hmem, hcode, herr, hframe⟩ :=
        arena_failure u base words huc hpu hue positive hb hi (hr.trans hs)
      refine ⟨10 + (arenaTrace u).length, ?_⟩
      rw [run_plus]
      change AllocationResult s (run (arenaTrace u).length u) base count
      refine ⟨?_, hcode, herr, ?_, ?_, ?_⟩
      · rw [hframe (.GPR 10) (by decide)]
        exact hw
      · simp only [show SszNative.Arena.wordsForBytes count = words from rfl, hs]
        exact ⟨hpc, hmem.trans hm⟩
      · rw [hframe (.GPR 11) (by decide)]
        exact hlast
      · intro f hpre harena
        exact (hframe f harena).trans (huf f hpre)
    | some reservation =>
      obtain ⟨hpc, hptr, hend, hmem, hinc, h13, h14, h15, hcode, herr, hframe⟩ :=
        arena_success u base words huc hpu hue positive hb hi reservation (hr.trans hs)
      have h19 : r (.GPR 19) u = r (.GPR 19) s := huf _ (by decide)
      have h8u : r (.GPR 8) u = r (.GPR 8) s := huf _ (by decide)
      have hcommit := mem_write_mem_bytes_of_mem_eq hm 8
        (r (.GPR 19) u + 16#64) (BitVec.ofNat 64 reservation.used)
      rw [h19] at hcommit hmem
      refine ⟨10 + (arenaTrace u).length, ?_⟩
      rw [run_plus]
      change AllocationResult s (run (arenaTrace u).length u) base count
      refine ⟨?_, hcode, herr, ?_, ?_, ?_⟩
      · rw [hframe (.GPR 10) (by decide)]
        exact hw
      · simp only [show SszNative.Arena.wordsForBytes count = words from rfl, hs]
        exact ⟨hpc, hptr, hend, hmem.trans hcommit, hinc.trans (congrArg (· + 1#64) h8u),
          h13, h14, h15⟩
      · rw [hframe (.GPR 11) (by decide)]
        exact hlast
      · intro f hpre harena
        exact (hframe f harena).trans (huf f hpre)
  · have hs : SszNative.Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat
        (arenaUsed s).toNat words = none :=
      (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ words positive).mpr
        (fun checks => hi checks.1)
    refine ⟨10, hw, huc, hue, ?_, hlast, ?_⟩
    · simp only [show SszNative.Arena.wordsForBytes count = words from rfl, hs]
      exact ⟨by simpa only [hi, ↓reduceIte] using hpp, hm⟩
    · intro f hpre _
      exact huf f hpre

end SszArm.UintCodec
