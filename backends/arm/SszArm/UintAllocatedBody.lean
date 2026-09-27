import SszArm.UintAllocatedMemory

namespace SszArm.UintCodec.Allocated

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem separated_of_regs {s t : ArmState} (hs : Tail.Separated s)
    (h0 : r (.GPR 0#5) t = r (.GPR 0#5) s) (h31 : r (.GPR 31#5) t = r (.GPR 31#5) s) :
    Tail.Separated t := by
  rcases hs with ⟨hl, hh, ho, hw, ha⟩
  exact ⟨by simpa only [h31] using hl, by simpa only [h31] using hh,
    by simpa only [h0] using ho, by simpa only [h0, h31] using hw,
    by simpa only [h0, h31] using ha⟩

private theorem allocation_input {s t : ArmState} {base : BitVec 64}
    {data : Ssz.Bytes} {count : Nat} (ho : Owned s data) (hi : Small.Input s data)
    (ha : AllocationResult s t base count) : Small.Input t data := by
  have hregs := ha.2.2.2.2.2
  have h2 := hregs (.GPR 2) (by decide) (by decide)
  have h3 := hregs (.GPR 3) (by decide) (by decide)
  have h31 := hregs (.GPR 31) (by decide) (by decide)
  refine ⟨h3.trans hi.length, hi.bounded, ?_, ?_, ?_, ?_⟩
  · simpa only [h2] using hi.range
  · simpa only [h31] using hi.stack
  · simpa only [h2, h31] using hi.separated
  · intro i hin
    rw [h2, BoolCodec.read_one]
    change t.mem (r (.GPR 2) s + BitVec.ofNat 64 i) = _
    rw [allocation_frame ho ha _
      (by have := hi.range; have := hi.separated; bv_omega)
      (by
        cases reservation s count with
        | none => trivial
        | some q =>
          have := hi.range
          have := ho.headerSource
          bv_omega)]
    simpa only [BoolCodec.read_one, read_mem, read_store] using hi.bytes i hin

/-- The cursor is unchanged on exhaustion and is exactly the checked committed
cursor on success, observed at the original arena-header address after RET. -/
def CursorAt (s t : ArmState) (result : Option SszNative.Arena.Reservation) : Prop :=
  read_mem_bytes 8 (r (.GPR 19) s + 16#64) t =
    match result with
    | none => read_mem_bytes 8 (r (.GPR 19) s + 16#64) s
    | some q => BitVec.ofNat 64 q.used

theorem CursorAt.prepend {s t u : ArmState} {data : Ssz.Bytes}
    {result : Option SszNative.Arena.Reservation} (h : Owned s data)
    (hs : Small.Stable s t) (hc : CursorAt t u result) : CursorAt s u result := by
  have h19 := hs.regs 19 (by decide)
  cases result with
  | none =>
    have hh := h.header_stable hs 16 (by decide)
    change read_mem_bytes 8 (r (.GPR 19) t + 16#64) t =
      read_mem_bytes 8 (r (.GPR 19) s + 16#64) s at hh
    rw [h19] at hh
    change read_mem_bytes 8 (r (.GPR 19) t + 16#64) u =
      read_mem_bytes 8 (r (.GPR 19) t + 16#64) t at hc
    rw [h19] at hc
    exact hc.trans hh
  | some q => simpa only [CursorAt, h19] using hc

private theorem allocation_cursor {s t : ArmState} {base : BitVec 64}
    {data : Ssz.Bytes} {count : Nat} (ho : Owned s data)
    (ha : AllocationResult s t base count) : CursorAt s t (reservation s count) := by
  have hh := ho.headerHigh
  have hs := ho.headerStack
  have hlo := ho.tail.stackLow
  have hx := ha.2.2.2.1
  change (match reservation s count with | none => _ | some _ => _) at hx
  cases hq : reservation s count with
  | none =>
    simp only [hq] at hx
    change read_mem_bytes 8 (r (.GPR 19) s + 16#64) t =
      read_mem_bytes 8 (r (.GPR 19) s + 16#64) s
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp hx.2) 8]
    unfold prepareSpill
    apply BoolCodec.read_mem_bytes_write_mem_bytes_disjoint <;> bv_omega
  | some q =>
    simp only [hq] at hx
    change read_mem_bytes 8 (r (.GPR 19) s + 16#64) t = BitVec.ofNat 64 q.used
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp hx.2.2.2.1) 8]
    apply BoolCodec.read_mem_bytes_write_mem_bytes_same
    bv_omega

private theorem tail_cursor {s t u : ArmState} {data : Ssz.Bytes} (ho : Owned s data)
    (h0 : r (.GPR 0#5) t = r (.GPR 0#5) s)
    (h31 : r (.GPR 31#5) t = r (.GPR 31#5) s) (hr : Tail.Returned t u) :
    read_mem_bytes 8 (r (.GPR 19) s + 16#64) u =
      read_mem_bytes 8 (r (.GPR 19) s + 16#64) t := by
  have hh := ho.headerHigh
  apply BoolCodec.read_bytes_congr
  intro i hi
  apply hr.frame
  · rw [h0]
    have := ho.headerOutput
    bv_omega
  · rw [h31]
    have := ho.headerStack
    bv_omega

/-- Complete actual allocating continuation, including arithmetic rejection and
insufficient or empty caller arenas. All stage inputs, the Large Nat image, and
activation transport are derived from initial ownership and the checked effects.
The result denotes the entire original input, not merely its significant prefix. -/
theorem runs (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes) (count : Nat)
    (hsig : count = SszNative.WordDecode.significantBytes data data.size)
    (hn : 8 < count) (hc : CodeAt s base) (hp : read_pc s = base + 4764#64)
    (he : read_err s = .None) (halign : CheckSPAlignment s)
    (hi : Small.Input s data) (ho : Owned s data)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (count-1))
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 count) :
    ∃ fuel t, run fuel s = t ∧ Returned s t count (reservation s count) ∧
      read_err t = .None ∧ Observation s t data (reservation s count) ∧
      CursorAt s t (reservation s count) := by
  have hcl : count ≤ data.size := by
    rw [hsig]
    exact SszNative.WordDecode.significantBytes_le data data.size
  have hbound : count < 2^63 := Nat.lt_of_le_of_lt hcl hi.bounded
  have hpositive : 0 < count := by omega
  have hwords : 0 < SszNative.Arena.wordsForBytes count := by
    have := (SszNative.Arena.wordsForBytes_bounds count).1
    omega
  obtain ⟨afuel, hac⟩ := allocation_runs s base count hc hp he halign
    hi.stack ho.outside_spill hpositive hbound (by
      change (r (.GPR 8) s).toNat = count - 1
      rw [h8]
      bv_omega)
  let a := run afuel s
  change AllocationResult s a base count at hac
  obtain ⟨hw, hacode, haerr, haeffect, hlast, haregs⟩ := hac
  have hac : AllocationResult s a base count := ⟨hw, hacode, haerr, haeffect, hlast, haregs⟩
  have ha0 := haregs (.GPR 0) (by decide) (by decide)
  have ha31 := haregs (.GPR 31) (by decide) (by decide)
  have ha2 := haregs (.GPR 2) (by decide) (by decide)
  have haa : CheckSPAlignment a := by
    have hsp : r (.GPR 31#5) a = r (.GPR 31#5) s := ha31
    simpa only [CheckSPAlignment, state_simp_rules, hsp] using halign
  have hat := separated_of_regs ho.tail ha0 ha31
  have haf := allocation_frame ho hac
  have hacursor := allocation_cursor ho hac
  cases hreserve : reservation s count with
  | none =>
    change (match reservation s count with | none => _ | some _ => _) at haeffect
    simp only [hreserve] at haeffect
    obtain ⟨hr, herr, hresult⟩ := Tail.scratch_exhausted_correct a base
      hacode haeffect.1 haerr haa hat
    have hf : Frame s a count (reservation s count) := by
      intro address _ hstack _
      apply haf address (by omega)
      simp only [hreserve]
    refine ⟨afuel + 56, run 56 a, ?_, ?_, herr, ?_, ?_⟩
    · rw [run_plus]
    · simpa only [hreserve] using returned_of_tail ho hpositive ha0 ha31 hf hr
    · change SszNative.UintCodec.scratchExhaustedAt (widthLoad (run 56 a))
        (r (.GPR 0) a).toNat at hresult
      simpa only [Observation, hreserve, ha0] using hresult
    · have hcursor : CursorAt s a none := by simpa only [hreserve] using hacursor
      exact (tail_cursor ho ha0 ha31 hr).trans hcursor
  | some q =>
    change (match reservation s count with | none => _ | some _ => _) at haeffect
    simp only [hreserve] at haeffect
    obtain ⟨hapc, hptr, _, _, ha8, ha13, ha14, ha15⟩ := haeffect
    have hv := ho.success_storage count hpositive q hreserve
    obtain ⟨qalign, qpos, qbound, qused, qcapacity, qlow, _, qhigh, qrange⟩ :=
      SszNative.Arena.success_properties _ _ _ _ hv.valid hwords q hreserve
    let pointer := BitVec.ofNat 64 q.pointer
    have hpn : pointer.toNat = q.pointer := Nat.mod_eq_of_lt qbound
    have har : Large.Area a data pointer count := by
      refine ⟨allocation_input ho hi hac, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hpn] using qpos
      · simpa only [hpn] using qalign
      · simpa only [hpn, ← SszNative.Arena.wordsForBytes_eq] using qrange
      · rw [hpn, ha2, ← SszNative.Arena.wordsForBytes_eq]
        have := hv.source
        omega
      · rw [hpn, ha31, ← SszNative.Arena.wordsForBytes_eq]
        have := hv.stack
        omega
    have ha8' : r (.GPR 8) a = BitVec.ofNat 64 count := by
      rw [ha8, h8]
      bv_omega
    have ha9' : r (.GPR 9) a = BitVec.ofNat 64 count :=
      (haregs (.GPR 9) (by decide) (by decide)).trans h9
    have ha10' : r (.GPR 10) a = BitVec.ofNat 64 ((count+7)/8) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, SszNative.Arena.wordsForBytes_eq]
      bv_omega
    have ha11' : r (.GPR 11) a = BitVec.ofNat 64 ((count+7)/8-1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hlast, SszNative.Arena.wordsForBytes_eq]
      bv_omega
    have ha12' : r (.GPR 12) a = pointer := by
      apply BitVec.eq_of_toNat_eq
      exact hptr.trans hpn.symm
    obtain ⟨lfuel, l, hlrun, hlstable, hlcode, hlerr, hlalign, hlar, hlpc,
      hl12, _, hllen, hlwords, hlvalue⟩ := Large.fill a base data pointer count
        hacode haerr haa har hapc (by omega) hcl ha8' ha9' ha10' ha11' ha12' ha13 ha14 ha15
    have hl0 := (hlstable.regs 0 (by decide)).trans ha0
    have hl31 := (hlstable.regs 31 (by decide)).trans ha31
    have hlt := separated_of_regs ho.tail hl0 hl31
    have hnat : Tail.NatPair l (r (.GPR 12) l) (r (.GPR 10) l)
        (Ssz.readUint data 0 data.size) := by
      rw [hl12]
      refine Or.inr ⟨SszNative.WordDecode.decodeWords data 0 count,
        hlar.nonnull, hlar.aligned, ?_, hllen, hlwords, ?_, Or.inr ⟨?_, ?_⟩⟩
      · simpa only [SszNative.WordDecode.decodeWords_length] using hlar.range
      · exact hlvalue.trans (by rw [hsig, SszNative.WordDecode.readUint_significantBytes])
      · change pointer.toNat + 8 * (SszNative.WordDecode.decodeWords data 0 count).length ≤
          (r (.GPR 0) l).toNat ∨ (r (.GPR 0) l).toNat + 76 ≤ pointer.toNat
        rw [hpn, SszNative.WordDecode.decodeWords_length, hl0,
          ← SszNative.Arena.wordsForBytes_eq]
        have := hv.output
        omega
      · change pointer.toNat + 8 * (SszNative.WordDecode.decodeWords data 0 count).length ≤
          (r (.GPR 31) l).toNat - 16 ∨ (r (.GPR 31) l).toNat + 192 ≤ pointer.toNat
        rw [hpn, SszNative.WordDecode.decodeWords_length, hl31,
          ← SszNative.Arena.wordsForBytes_eq]
        have := hv.stack
        omega
    have hlf : Frame s l count (reservation s count) := by
      intro address hout hstack hextra
      have hx :
          (address.toNat < (r (.GPR 19) s).toNat + 16 ∨
            (r (.GPR 19) s).toNat + 24 ≤ address.toNat) ∧
          (address.toNat < q.pointer ∨
            q.pointer + 8 * SszNative.Arena.wordsForBytes count ≤ address.toNat) := by
        simpa only [ExtraOutside, hreserve] using hextra
      have hs : address.toNat < (r (.GPR 31) s).toNat - 16 ∨
          (r (.GPR 31) s).toNat ≤ address.toNat := by omega
      exact (hlstable.frame address
        (by simpa only [hpn, ← SszNative.Arena.wordsForBytes_eq] using hx.2)
        (by simpa only [ha31] using hs)).trans
          (haf address hs (by simpa only [hreserve] using hx.1))
    obtain ⟨hr, herr, hresult⟩ := Tail.success_correct l base
      (Ssz.readUint data 0 data.size) hlcode hlpc hlerr hlalign hlt hnat
    refine ⟨afuel + lfuel + 22, run 22 l, ?_, ?_, herr, ?_, ?_⟩
    · rw [run_plus, run_plus]
      change run 22 (run lfuel a) = run 22 l
      rw [hlrun]
    · simpa only [hreserve] using returned_of_tail ho hpositive hl0 hl31 hlf hr
    · change SszNative.UintCodec.ResultAt (widthLoad (run 22 l))
        (r (.GPR 0) l).toNat (.ok (.uint (Ssz.readUint data 0 data.size))) at hresult
      simpa only [Observation, hreserve, hl0] using hresult
    · have hcursor : CursorAt s a (some q) := by simpa only [hreserve] using hacursor
      have hfillcursor : read_mem_bytes 8 (r (.GPR 19) s + 16#64) l =
          read_mem_bytes 8 (r (.GPR 19) s + 16#64) a := by
        have hh := ho.headerHigh
        have hheader := hv.header
        have hstack := ho.headerStack
        apply BoolCodec.read_bytes_congr
        intro i hi
        apply hlstable.frame
        · rw [hpn, ← SszNative.Arena.wordsForBytes_eq]
          bv_omega
        · rw [ha31]
          bv_omega
      exact (tail_cursor ho hl0 hl31 hr).trans (hfillcursor.trans hcursor)

end SszArm.UintCodec.Allocated

namespace SszArm.UintCodec

/-- Allocating continuation at the exact boundary exposed by
`prefix_finish_or_allocate`; the source retains its original full length. -/
theorem allocated_body_runs (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (hn : 8 < SszNative.WordDecode.significantBytes data data.size)
    (hc : CodeAt s base) (hp : read_pc s = base + 4764#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Small.Input s data) (ho : Allocated.Owned s data)
    (h8 : r (.GPR 8) s = BitVec.ofNat 64 (SszNative.WordDecode.significantBytes data data.size-1))
    (h9 : r (.GPR 9) s = BitVec.ofNat 64 (SszNative.WordDecode.significantBytes data data.size)) :
    ∃ fuel t, run fuel s = t ∧
      Allocated.Returned s t (SszNative.WordDecode.significantBytes data data.size)
        (Allocated.reservation s (SszNative.WordDecode.significantBytes data data.size)) ∧
      read_err t = .None ∧ Allocated.Observation s t data
        (Allocated.reservation s (SszNative.WordDecode.significantBytes data data.size)) ∧
      Allocated.CursorAt s t
        (Allocated.reservation s (SszNative.WordDecode.significantBytes data data.size)) :=
  Allocated.runs s base data _ rfl hn hc hp he ha hi ho h8 h9

end SszArm.UintCodec
