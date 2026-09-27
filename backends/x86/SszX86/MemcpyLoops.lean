import SszX86.MemcpyExec

namespace SszX86

open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def memcpyFinal (base : Int64) (src : MachineData) (xs : List UInt8)
    (R : DataMem → Prop) : MachineState → Prop :=
  fun st =>
    st.2 = base + 56 ∧
    st.1.regs.rdx.toBitVec = 0 ∧
    MemcpyFrame src st.1 ∧
    CopyMem st.1.dmem src.regs.rsi.toBitVec src.regs.rdi.toBitVec xs xs R

private theorem memcpyTest_frame (s : MachineData) (af : Bool) :
    MemcpyFrame s (memcpyTestState s af) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp [memcpyTestState, Reg64s.get64]

private theorem memcpyByteState_count (s : MachineData) (v : Int) (n : Nat)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 n) (hpos : 0 < n) :
    (memcpyByteState s v).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 1) := by
  change s.regs.rdx.toBitVec - 1#64 = _
  rw [hcount]
  exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) (by omega)

private theorem memcpyBulkState_count (s : MachineData) (v : Int) (n : Nat)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 n) (h8 : 8 ≤ n) :
    (memcpyBulkState s v).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 8) := by
  change s.regs.rdx.toBitVec - 8#64 = _
  rw [hcount]
  exact BitVec.ofNat_sub_ofNat_of_le n 8 (by decide) h8

private theorem memcpy_byte_loop (base : Int64) :
  ∀ n (s : MachineData) (xs old : List UInt8) (R : DataMem → Prop),
    xs.length = n → old.length = n → s.regs.rdx.toBitVec = BitVec.ofNat 64 n →
    0 < n → n < 8 → n < 2^64 →
    CopyMem s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old R →
    Eventually (memcpyStep base) (memcpyFinal base s xs R) (s, base + 38) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih s xs old R hxs hold hcount hpos hlt hb hmem
  have hlen : old.length = xs.length := by omega
  have hchunk := memcpy_chunk s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old R 1 hlen
    (by omega) (by omega) hmem
  rcases hchunk with ⟨hs, hd, hcopy⟩
  let v : Int := Int.ofBytes (xs.take 1)
  let R' : DataMem → Prop :=
    Eq ((xs.take 1).At s.regs.rdi.toBitVec) ⋆
      (Eq ((xs.take 1).At s.regs.rsi.toBitVec) ⋆ R)
  have hbytes : Int.toBytes 1 (BitVec.ofInt 8 v).toInt = xs.take 1 :=
    memcpy_roundtrip 1 (xs.take 1) (List.length_take_of_le (by omega))
  have hstate : CopyMem (memcpyByteState s (Int.ofBytes (xs.take 1))).dmem
      (s.regs.rsi.toBitVec + 1) (s.regs.rdi.toBitVec + 1)
      (xs.drop 1) (old.drop 1) R' := by
    dsimp (config := {instances := true}) [memcpyByteState, Mem.storeInt]
    rw [hbytes]
    exact hcopy
  have hz : (memcpyByteState s (Int.ofBytes (xs.take 1))).status.zf = decide (n = 1) := by
    change (memcpySubFlags s.regs.rdx.toBitVec 1#64).zf = _
    rw [hcount]
    exact memcpy_zf_sub1 n hb
  by_cases hn1 : n = 1
  · subst hn1
    have hdrop : old.drop 1 = xs.drop 1 := by
      simp [List.drop_eq_nil_of_le (show old.length ≤ 1 by omega),
        List.drop_eq_nil_of_le (show xs.length ≤ 1 by omega)]
    rw [hdrop] at hstate
    have hcopyFinal : CopyMem (memcpyByteState s (Int.ofBytes (xs.take 1))).dmem
        s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs xs R := by
      exact memcpy_join _ _ _ xs R 1 (by omega) (by omega) hstate
    have hdone : memcpyFinal base s xs R
        (memcpyByteState s (Int.ofBytes (xs.take 1)), base + 56) := by
      refine ⟨rfl, ?_, ?_, hcopyFinal⟩
      · simp [memcpyByteState, hcount]
      exact memcpyByte_frame s (Int.ofBytes (xs.take 1))
    have hhp : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyByteState s (Int.ofBytes (xs.take 1)),
          if (memcpyByteState s (Int.ofBytes (xs.take 1))).status.zf then base + 56 else base + 38) := by
      simpa [hz] using (Eventually.done _ hdone)
    exact memcpy_byte_runs base s (Int.ofBytes (xs.take 1)) (Int.ofBytes (old.take 1))
      (memcpyFinal base s xs R) hs hd hhp
  · have hgt1 : 1 < n := by omega
    have hcount' : (memcpyByteState s (Int.ofBytes (xs.take 1))).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 1) := by
      exact memcpyByteState_count s (Int.ofBytes (xs.take 1)) n hcount hpos
    have hrec := ih (n - 1) (by omega) (memcpyByteState s (Int.ofBytes (xs.take 1)))
      (xs.drop 1) (old.drop 1) R' (by simp [hxs])
      (by simp [hold])
      hcount' (by omega) (by omega) (by omega) hstate
    have hstrength : ∀ st,
        memcpyFinal base (memcpyByteState s (Int.ofBytes (xs.take 1))) (xs.drop 1) R' st →
        memcpyFinal base s xs R st := by
      intro st hst
      rcases hst with ⟨hpc, hrdx, hframe, hcopy'⟩
      refine ⟨hpc, hrdx,
        memcpyFrame_trans (memcpyByte_frame s (Int.ofBytes (xs.take 1))) hframe, ?_⟩
      apply memcpy_join _ _ _ xs R 1 (by omega) (by omega)
      simpa (config := {instances := true}) [memcpyByteState, R'] using hcopy'
    have hrec' : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyByteState s (Int.ofBytes (xs.take 1)), base + 38) := by
      exact eventually_weaken _ _ _ _ hstrength hrec
    have hhp : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyByteState s (Int.ofBytes (xs.take 1)),
          if (memcpyByteState s (Int.ofBytes (xs.take 1))).status.zf then base + 56 else base + 38) := by
      simpa [hz, hn1] using hrec'
    exact memcpy_byte_runs base s (Int.ofBytes (xs.take 1)) (Int.ofBytes (old.take 1))
      (memcpyFinal base s xs R) hs hd hhp

private theorem memcpy_tail_loop (base : Int64) :
  ∀ n (s : MachineData) (xs old : List UInt8) (R : DataMem → Prop),
    xs.length = n → old.length = n → s.regs.rdx.toBitVec = BitVec.ofNat 64 n →
    n < 8 → n < 2^64 →
    CopyMem s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old R →
    Eventually (memcpyStep base) (memcpyFinal base s xs R) (s, base + 33) := by
  intro n s xs old R hxs hold hcount hlt hb hmem
  by_cases hn0 : n = 0
  · subst n
    have hx : xs = [] := by
      cases xs <;> simp_all
    have ho : old = [] := by
      cases old <;> simp_all
    subst hx
    subst ho
    have hhp : ∀ af, Eventually (memcpyStep base) (memcpyFinal base s [] R)
        (memcpyTestState s af,
          if (memcpyTestState s af).regs.rdx.toBitVec == 0 then base + 56 else base + 38) := by
      intro af
      have hframe : MemcpyFrame s (memcpyTestState s af) := memcpyTest_frame s af
      have hcopy : CopyMem (memcpyTestState s af).dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec [] [] R := by
        simpa [memcpyTestState] using hmem
      have hdone : memcpyFinal base s [] R (memcpyTestState s af, base + 56) := by
        exact ⟨rfl, hcount, hframe, hcopy⟩
      simpa [memcpyTestState, hcount] using (Eventually.done _ hdone)
    exact memcpy_tail_runs base s (memcpyFinal base s [] R) hhp
  · have hpos : 0 < n := by omega
    have hhp : ∀ af, Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyTestState s af,
          if (memcpyTestState s af).regs.rdx.toBitVec == 0 then base + 56 else base + 38) := by
      intro af
      have hcountAf : (memcpyTestState s af).regs.rdx.toBitVec = BitVec.ofNat 64 n := by
        simp [memcpyTestState, hcount]
      have hrec := memcpy_byte_loop base n (memcpyTestState s af) xs old R hxs hold hcountAf
        hpos hlt hb hmem
      have hstrength : ∀ st,
          memcpyFinal base (memcpyTestState s af) xs R st → memcpyFinal base s xs R st := by
        intro st hst
        rcases hst with ⟨hpc, hrdx, hframe, hcopy⟩
        exact ⟨hpc, hrdx, memcpyFrame_trans (memcpyTest_frame s af) hframe, hcopy⟩
      have hrec' : Eventually (memcpyStep base) (memcpyFinal base s xs R)
          (memcpyTestState s af, base + 38) := by
        exact eventually_weaken _ _ _ _ hstrength hrec
      have hz : s.regs.rdx.toBitVec ≠ 0 := by
        intro he
        have := congrArg BitVec.toNat he
        simp [hcount, Nat.mod_eq_of_lt hb] at this
        omega
      simpa only [memcpyTestState, beq_iff_eq, hz, ite_false] using hrec'
    exact memcpy_tail_runs base s (memcpyFinal base s xs R) hhp

private theorem memcpy_bulk_loop (base : Int64) :
  ∀ n (s : MachineData) (xs old : List UInt8) (R : DataMem → Prop),
    xs.length = n → old.length = n → s.regs.rdx.toBitVec = BitVec.ofNat 64 n →
    8 ≤ n → n < 2^64 →
    CopyMem s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old R →
    Eventually (memcpyStep base) (memcpyFinal base s xs R) (s, base + 9) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih s xs old R hxs hold hcount h8 hb hmem
  have hlen : old.length = xs.length := by omega
  have hchunk := memcpy_chunk s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old R 8 hlen
    (by omega) (by omega) hmem
  rcases hchunk with ⟨hs, hd, hcopy⟩
  let v : Int := Int.ofBytes (xs.take 8)
  let R' : DataMem → Prop :=
    Eq ((xs.take 8).At s.regs.rdi.toBitVec) ⋆
      (Eq ((xs.take 8).At s.regs.rsi.toBitVec) ⋆ R)
  have hbytes : Int.toBytes 8 (BitVec.ofInt 64 v).toInt = xs.take 8 :=
    memcpy_roundtrip 8 (xs.take 8) (List.length_take_of_le (by omega))
  have hstate : CopyMem (memcpyBulkState s (Int.ofBytes (xs.take 8))).dmem
      (s.regs.rsi.toBitVec + 8) (s.regs.rdi.toBitVec + 8)
      (xs.drop 8) (old.drop 8) R' := by
    dsimp (config := {instances := true}) [memcpyBulkState, Mem.storeInt]
    rw [hbytes]
    exact hcopy
  have hcount' : (memcpyBulkState s (Int.ofBytes (xs.take 8))).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 8) := by
    exact memcpyBulkState_count s (Int.ofBytes (xs.take 8)) n hcount h8
  have hframe : MemcpyFrame s (memcpyBulkState s (Int.ofBytes (xs.take 8))) := memcpyBulk_frame s (Int.ofBytes (xs.take 8))
  have hcf : (memcpyBulkState s (Int.ofBytes (xs.take 8))).status.cf =
      decide (n - 8 < 8) := by
    change (memcpySubFlags (memcpyBulkState s (Int.ofBytes (xs.take 8))).regs.rdx.toBitVec 8#64).cf = _
    rw [hcount']
    exact memcpy_cf_sub8 (n - 8) (by omega)
  by_cases hsmall : n - 8 < 8
  · have hrec := memcpy_tail_loop base (n - 8) (memcpyBulkState s (Int.ofBytes (xs.take 8)))
        (xs.drop 8) (old.drop 8) R' (by simp [hxs])
        (by simp [hold]) hcount' hsmall (by omega) hstate
    have hstrength : ∀ st,
        memcpyFinal base (memcpyBulkState s (Int.ofBytes (xs.take 8))) (xs.drop 8) R' st →
        memcpyFinal base s xs R st := by
      intro st hst
      rcases hst with ⟨hpc, hrdx, hframe', hcopy'⟩
      refine ⟨hpc, hrdx, memcpyFrame_trans hframe hframe', ?_⟩
      apply memcpy_join _ _ _ xs R 8 (by omega) (by omega)
      simpa (config := {instances := true}) [memcpyBulkState, R'] using hcopy'
    have hrec' : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyBulkState s (Int.ofBytes (xs.take 8)), base + 33) := by
      exact eventually_weaken _ _ _ _ hstrength hrec
    have hhp : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyBulkState s (Int.ofBytes (xs.take 8)),
          if (memcpyBulkState s (Int.ofBytes (xs.take 8))).status.cf then base + 33 else base + 9) := by
      simpa [hcf, hsmall] using hrec'
    exact memcpy_bulk_runs base s (Int.ofBytes (xs.take 8)) (Int.ofBytes (old.take 8))
      (memcpyFinal base s xs R) hs hd hhp
  · have hbig : 8 ≤ n - 8 := by omega
    have hrec := ih (n - 8) (by omega) (memcpyBulkState s (Int.ofBytes (xs.take 8)))
      (xs.drop 8) (old.drop 8) R' (by simp [hxs])
      (by simp [hold]) hcount' hbig (by omega) hstate
    have hstrength : ∀ st,
        memcpyFinal base (memcpyBulkState s (Int.ofBytes (xs.take 8))) (xs.drop 8) R' st →
        memcpyFinal base s xs R st := by
      intro st hst
      rcases hst with ⟨hpc, hrdx, hframe', hcopy'⟩
      refine ⟨hpc, hrdx, memcpyFrame_trans hframe hframe', ?_⟩
      apply memcpy_join _ _ _ xs R 8 (by omega) (by omega)
      simpa (config := {instances := true}) [memcpyBulkState, R'] using hcopy'
    have hrec' : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyBulkState s (Int.ofBytes (xs.take 8)), base + 9) := by
      exact eventually_weaken _ _ _ _ hstrength hrec
    have hhp : Eventually (memcpyStep base) (memcpyFinal base s xs R)
        (memcpyBulkState s (Int.ofBytes (xs.take 8)),
          if (memcpyBulkState s (Int.ofBytes (xs.take 8))).status.cf then base + 33 else base + 9) := by
      simpa [hcf, hsmall] using hrec'
    exact memcpy_bulk_runs base s (Int.ofBytes (xs.take 8)) (Int.ofBytes (old.take 8))
      (memcpyFinal base s xs R) hs hd hhp

/-- Loop-only correctness: from the entry state and a count equal to the source
length, the loop reaches `copy_done` with the destination copied and the entry
frame preserved. The return itself is handled separately. -/
theorem memcpy_loops_runs (base : Int64) (s : MachineData) (xs old : List UInt8)
    (R : DataMem → Prop)
    (hlen : old.length = xs.length)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length)
    (hb : xs.length < 2^64)
    (hmem : CopyMem s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old R) :
    Eventually (memcpyStep base) (memcpyFinal base (memcpyEntryState s) xs R) (s, base) := by
  have hentryCount : (memcpyEntryState s).regs.rdx.toBitVec = BitVec.ofNat 64 xs.length := by
    simpa [memcpyEntryState] using hcount
  have hcf : (memcpyEntryState s).status.cf = decide (xs.length < 8) := by
    simpa [memcpyEntryState, hcount] using memcpy_cf_sub8 xs.length hb
  have hentry : Eventually (memcpyStep base)
      (memcpyFinal base (memcpyEntryState s) xs R)
      (memcpyEntryState s,
        if (memcpyEntryState s).status.cf then base + 33 else base + 9) := by
    by_cases hlt8 : xs.length < 8
    · have htail := memcpy_tail_loop base xs.length (memcpyEntryState s) xs old R
        (by rfl) hlen hentryCount hlt8 hb hmem
      simpa [hcf, hlt8] using htail
    · have hbulk := memcpy_bulk_loop base xs.length (memcpyEntryState s) xs old R
        (by rfl) hlen hentryCount (by omega) hb hmem
      simpa [hcf, hlt8] using hbulk
  exact memcpy_entry_runs base s (memcpyFinal base (memcpyEntryState s) xs R) hentry

end SszX86
