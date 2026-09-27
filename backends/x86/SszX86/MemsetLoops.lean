import SszX86.MemsetExec

namespace SszX86

open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def memsetFinal (base : Int64) (src : MachineData) (n : Nat) (b : UInt8)
    (R : DataMem → Prop) : MachineState → Prop :=
  fun st =>
    st.2 = base + 62 ∧
    st.1.regs.rdx.toBitVec = 0 ∧
    MemsetFrame src st.1 ∧
    FillMem st.1.dmem src.regs.rdi.toBitVec (List.replicate n b) R

private theorem memsetByteState_count (s : MachineData) (n : Nat)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 n) (hpos : 0 < n) :
    (memsetByteState s).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 1) := by
  change s.regs.rdx.toBitVec - 1#64 = _
  rw [hcount]
  exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) (by omega)

private theorem memsetBulkState_count (s : MachineData) (n : Nat)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 n) (h8 : 8 ≤ n) :
    (memsetBulkState s).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 8) := by
  change s.regs.rdx.toBitVec - 8#64 = _
  rw [hcount]
  exact BitVec.ofNat_sub_ofNat_of_le n 8 (by decide) h8

/-- The byte instruction stores SIL, including its signed-to-byte conversion. -/
private theorem memsetByte_bytes (s : MachineData) :
    Int.toBytes 1 (s.regs.rsi.toBitVec.setWidth 8).toInt = [memsetByte s] := by
  have hv : BitVec.ofInt 8 (memsetByteValue (memsetByte s)) =
      s.regs.rsi.toBitVec.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp (config := {instances := true})
      [memsetByteValue, memsetByte, BitVec.toNat_setWidth]
    rfl
  have h := memset_byte_signed_roundtrip (memsetByte s)
  rw [hv] at h
  exact h

/-- The setup's actual multiplication is the little-endian repeated byte word. -/
private theorem memsetSetup_broadcast (s : MachineData) (status : StatusFlags) :
    (memsetSetupState s status).regs.r9.toBitVec =
      BitVec.ofInt 64 (memsetFillValue (memsetByte s)) := by
  change 0x0101010101010101#64 * (s.regs.rsi.toBitVec.setWidth 8).setWidth 64 = _
  have hcast (n : Nat) : BitVec.ofInt 64 (Int.ofNat n) = BitVec.ofNat 64 n := rfl
  have hc : memsetBroadcast 8 = 72340172838076673 := by simp [memsetBroadcast]
  rw [memsetFillValue, hcast, BitVec.ofNat_mul, hc]
  have hlow : BitVec.ofNat 64 (memsetByte s).toNat =
      (s.regs.rsi.toBitVec.setWidth 8).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [memsetByte, BitVec.toNat_setWidth]
  rw [hlow]
  exact BitVec.mul_comm _ _

private theorem memsetSetup_frame (s : MachineData) (status : StatusFlags) :
    MemsetFrame s (memsetSetupState s status) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4
  cases r <;> simp_all [memsetSetupState, Reg64s.get64]

private theorem memset_join_replicate (m : DataMem) (dst : BitVec 64)
    (n : Nat) (b : UInt8) (R : DataMem → Prop) (k : Nat)
    (hk : k ≤ n) (hb : n ≤ 2^64)
    (hm : FillMem m (dst + BitVec.ofNat 64 k) (List.replicate (n - k) b)
      (Eq ((List.replicate k b).At dst) ⋆ R)) :
    FillMem m dst (List.replicate n b) R := by
  apply memset_join m dst (List.replicate n b) R k (by simpa) (by simpa)
  simpa [Nat.min_eq_left hk] using hm

private theorem memset_byte_loop (base : Int64) :
  ∀ n (s : MachineData) (b : UInt8) (old : List UInt8) (R : DataMem → Prop),
    old.length = n → s.regs.rdx.toBitVec = BitVec.ofNat 64 n →
    memsetByte s = b → 0 < n → n < 8 → n < 2^64 →
    FillMem s.dmem s.regs.rdi.toBitVec old R →
    Eventually (memsetStep base) (memsetFinal base s n b R) (s, base + 49) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih s b old R hlen hcount hbyte hpos hlt hb hmem
  have hchunk := memset_chunk s.dmem s.regs.rdi.toBitVec old [b] R 1
    rfl (by omega) (by omega) hmem
  rcases hchunk with ⟨hd, hfill⟩
  let R' : DataMem → Prop := Eq ((List.replicate 1 b).At s.regs.rdi.toBitVec) ⋆ R
  have hbytes : Int.toBytes 1 (s.regs.rsi.toBitVec.setWidth 8).toInt = [b] := by
    simpa [hbyte] using memsetByte_bytes s
  have hstate : FillMem (memsetByteState s).dmem
      (s.regs.rdi.toBitVec + 1) (old.drop 1) R' := by
    dsimp (config := {instances := true}) [memsetByteState, Mem.storeInt]
    rw [hbytes]
    exact hfill
  have hz : (memsetByteState s).status.zf = decide (n = 1) := by
    change (memcpySubFlags s.regs.rdx.toBitVec 1#64).zf = _
    rw [hcount]
    exact memcpy_zf_sub1 n hb
  by_cases hn1 : n = 1
  · have hdrop : old.drop 1 = List.replicate (1 - 1) b := by
      simp [List.drop_eq_nil_of_le (show old.length ≤ 1 by omega)]
    rw [hdrop] at hstate
    have hfillFinal : FillMem (memsetByteState s).dmem
        s.regs.rdi.toBitVec (List.replicate 1 b) R := by
      exact memset_join_replicate _ _ 1 b R 1 (by omega) (by omega) hstate
    have hdone : memsetFinal base s 1 b R (memsetByteState s, base + 62) := by
      refine ⟨rfl, ?_, memsetByte_frame s, hfillFinal⟩
      simp [memsetByteState, hcount, hn1]
    have hhp : Eventually (memsetStep base) (memsetFinal base s 1 b R)
        (memsetByteState s,
          if (memsetByteState s).status.zf then base + 62 else base + 49) := by
      simpa [hz, hn1] using (Eventually.done _ hdone)
    simpa [hn1] using memset_byte_runs base s (Int.ofBytes (old.take 1))
      (memsetFinal base s 1 b R) hd hhp
  · have hcount' : (memsetByteState s).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 1) :=
      memsetByteState_count s n hcount hpos
    have hrec := ih (n - 1) (by omega) (memsetByteState s) b (old.drop 1) R'
      (by simp [hlen]) hcount' hbyte (by omega) (by omega) (by omega) hstate
    have hstrength : ∀ st,
        memsetFinal base (memsetByteState s) (n - 1) b R' st →
        memsetFinal base s n b R st := by
      intro st hst
      rcases hst with ⟨hpc, hrdx, hframe, hfill'⟩
      refine ⟨hpc, hrdx, memsetFrame_trans (memsetByte_frame s) hframe, ?_⟩
      apply memset_join_replicate _ _ n b R 1 (by omega) (by omega)
      simpa (config := {instances := true}) [memsetByteState, R'] using hfill'
    have hrec' : Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetByteState s, base + 49) :=
      eventually_weaken _ _ _ _ hstrength hrec
    have hhp : Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetByteState s,
          if (memsetByteState s).status.zf then base + 62 else base + 49) := by
      simpa [hz, hn1] using hrec'
    exact memset_byte_runs base s (Int.ofBytes (old.take 1))
      (memsetFinal base s n b R) hd hhp

private theorem memset_tail_loop (base : Int64) :
  ∀ n (s : MachineData) (b : UInt8) (old : List UInt8) (R : DataMem → Prop),
    old.length = n → s.regs.rdx.toBitVec = BitVec.ofNat 64 n →
    memsetByte s = b → n < 8 → n < 2^64 →
    FillMem s.dmem s.regs.rdi.toBitVec old R →
    Eventually (memsetStep base) (memsetFinal base s n b R) (s, base + 44) := by
  intro n s b old R hlen hcount hbyte hlt hb hmem
  by_cases hn0 : n = 0
  · subst n
    have ho : old = [] := by
      cases old <;> simp_all
    subst old
    have hhp : ∀ af, Eventually (memsetStep base) (memsetFinal base s 0 b R)
        (memsetTestState s af,
          if s.regs.rdx.toBitVec == 0 then base + 62 else base + 49) := by
      intro af
      have hdone : memsetFinal base s 0 b R (memsetTestState s af, base + 62) :=
        ⟨rfl, hcount, memsetTest_frame s af, hmem⟩
      simpa [hcount] using (Eventually.done _ hdone)
    exact memset_tail_runs base s (memsetFinal base s 0 b R) hhp
  · have hpos : 0 < n := by omega
    have hhp : ∀ af, Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetTestState s af,
          if s.regs.rdx.toBitVec == 0 then base + 62 else base + 49) := by
      intro af
      have hrec := memset_byte_loop base n (memsetTestState s af) b old R
        hlen hcount hbyte hpos hlt hb hmem
      have hstrength : ∀ st,
          memsetFinal base (memsetTestState s af) n b R st →
          memsetFinal base s n b R st := by
        intro st hst
        rcases hst with ⟨hpc, hrdx, hframe, hfill⟩
        exact ⟨hpc, hrdx, memsetFrame_trans (memsetTest_frame s af) hframe, hfill⟩
      have hrec' : Eventually (memsetStep base) (memsetFinal base s n b R)
          (memsetTestState s af, base + 49) :=
        eventually_weaken _ _ _ _ hstrength hrec
      have hz : s.regs.rdx.toBitVec ≠ 0 := by
        intro he
        have := congrArg BitVec.toNat he
        simp [hcount, Nat.mod_eq_of_lt hb] at this
        omega
      simpa only [beq_iff_eq, hz, ite_false] using hrec'
    exact memset_tail_runs base s (memsetFinal base s n b R) hhp

private theorem memset_bulk_loop (base : Int64) :
  ∀ n (s : MachineData) (b : UInt8) (old : List UInt8) (R : DataMem → Prop),
    old.length = n → s.regs.rdx.toBitVec = BitVec.ofNat 64 n →
    memsetByte s = b → s.regs.r9.toBitVec = BitVec.ofInt 64 (memsetFillValue b) →
    8 ≤ n → n < 2^64 →
    FillMem s.dmem s.regs.rdi.toBitVec old R →
    Eventually (memsetStep base) (memsetFinal base s n b R) (s, base + 27) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih s b old R hlen hcount hbyte hword h8 hb hmem
  have hchunk := memset_chunk s.dmem s.regs.rdi.toBitVec old (List.replicate 8 b) R 8
    (by simp) (by omega) (by omega) hmem
  rcases hchunk with ⟨hd, hfill⟩
  let R' : DataMem → Prop := Eq ((List.replicate 8 b).At s.regs.rdi.toBitVec) ⋆ R
  have hbytes : Int.toBytes 8 s.regs.r9.toBitVec.toInt = List.replicate 8 b := by
    rw [hword]
    exact memset_signed_roundtrip b
  have hstate : FillMem (memsetBulkState s).dmem
      (s.regs.rdi.toBitVec + 8) (old.drop 8) R' := by
    dsimp (config := {instances := true}) [memsetBulkState, Mem.storeInt]
    rw [hbytes]
    exact hfill
  have hcount' : (memsetBulkState s).regs.rdx.toBitVec = BitVec.ofNat 64 (n - 8) :=
    memsetBulkState_count s n hcount h8
  have hframe : MemsetFrame s (memsetBulkState s) := memsetBulk_frame s
  have hcf : (memsetBulkState s).status.cf = decide (n - 8 < 8) := by
    change (memcpySubFlags (memsetBulkState s).regs.rdx.toBitVec 8#64).cf = _
    rw [hcount']
    exact memcpy_cf_sub8 (n - 8) (by omega)
  have hstrength : ∀ st,
      memsetFinal base (memsetBulkState s) (n - 8) b R' st →
      memsetFinal base s n b R st := by
    intro st hst
    rcases hst with ⟨hpc, hrdx, hframe', hfill'⟩
    refine ⟨hpc, hrdx, memsetFrame_trans hframe hframe', ?_⟩
    apply memset_join_replicate _ _ n b R 8 h8 (by omega)
    simpa (config := {instances := true}) [memsetBulkState, R'] using hfill'
  by_cases hsmall : n - 8 < 8
  · have hrec := memset_tail_loop base (n - 8) (memsetBulkState s) b (old.drop 8) R'
        (by simp [hlen]) hcount' hbyte hsmall (by omega) hstate
    have hrec' : Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetBulkState s, base + 44) :=
      eventually_weaken _ _ _ _ hstrength hrec
    have hhp : Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetBulkState s,
          if (memsetBulkState s).status.cf then base + 44 else base + 27) := by
      simpa [hcf, hsmall] using hrec'
    exact memset_bulk_runs base s (Int.ofBytes (old.take 8))
      (memsetFinal base s n b R) hd hhp
  · have hrec := ih (n - 8) (by omega) (memsetBulkState s) b (old.drop 8) R'
        (by simp [hlen]) hcount' hbyte hword (by omega) (by omega) hstate
    have hrec' : Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetBulkState s, base + 27) :=
      eventually_weaken _ _ _ _ hstrength hrec
    have hhp : Eventually (memsetStep base) (memsetFinal base s n b R)
        (memsetBulkState s,
          if (memsetBulkState s).status.cf then base + 44 else base + 27) := by
      simpa [hcf, hsmall] using hrec'
    exact memset_bulk_runs base s (Int.ofBytes (old.take 8))
      (memsetFinal base s n b R) hd hhp

/-- Execute the actual entry guard, optional broadcast and loops. The byte
invariant is tied to RSI, and the word invariant to the actual broadcast in R9.
Sub-word fills, including length zero, skip the broadcast instructions. -/
theorem memset_loops_runs (base : Int64) (s : MachineData) (n : Nat)
    (old : List UInt8) (R : DataMem → Prop)
    (hlen : old.length = n)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 n)
    (hb : n < 2^64)
    (hmem : FillMem s.dmem s.regs.rdi.toBitVec old R) :
    Eventually (memsetStep base)
      (memsetFinal base (memcpyEntryState s) n (memsetByte s) R) (s, base) := by
  have hentryCount : (memcpyEntryState s).regs.rdx.toBitVec = BitVec.ofNat 64 n :=
    hcount
  have hcf : (memcpyEntryState s).status.cf = decide (n < 8) := by
    simpa [memcpyEntryState, hcount] using memcpy_cf_sub8 n hb
  have hentry : Eventually (memsetStep base)
      (memsetFinal base (memcpyEntryState s) n (memsetByte s) R)
      (memcpyEntryState s,
        if (memcpyEntryState s).status.cf then base + 44 else base + 9) := by
    by_cases hlt8 : n < 8
    · have htail := memset_tail_loop base n (memcpyEntryState s) (memsetByte s) old R
        hlen hentryCount rfl hlt8 hb hmem
      simpa [hcf, hlt8] using htail
    · have hsetup : Eventually (memsetStep base)
          (memsetFinal base (memcpyEntryState s) n (memsetByte s) R)
          (memcpyEntryState s, base + 9) := by
        apply memset_setup_runs
        intro status
        have hbulk := memset_bulk_loop base n (memsetSetupState (memcpyEntryState s) status)
          (memsetByte s) old R hlen hentryCount rfl
          (memsetSetup_broadcast (memcpyEntryState s) status) (by omega) hb hmem
        apply eventually_weaken _ _ _ _ _ hbulk
        intro st hst
        rcases hst with ⟨hpc, hrdx, hframe, hfill⟩
        exact ⟨hpc, hrdx,
          memsetFrame_trans (memsetSetup_frame (memcpyEntryState s) status) hframe, hfill⟩
      simpa [hcf, hlt8] using hsetup
  exact memset_entry_runs base s
    (memsetFinal base (memcpyEntryState s) n (memsetByte s) R) hentry

end SszX86
