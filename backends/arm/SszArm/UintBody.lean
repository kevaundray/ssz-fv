import SszArm.UintAllocatedBody

namespace SszArm.UintCodec.Body

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Allocation is attempted only after a matching width and a Large trimmed value. -/
def needsAllocation (width : Nat) (data : Ssz.Bytes) : Prop :=
  width = data.size ∧ 8 < SszNative.WordDecode.significantBytes data data.size

instance (width : Nat) (data : Ssz.Bytes) : Decidable (needsAllocation width data) :=
  inferInstanceAs (Decidable (width = data.size ∧
    8 < SszNative.WordDecode.significantBytes data data.size))

def reservation (s : ArmState) (width : Nat) (data : Ssz.Bytes) :
    Option SszNative.Arena.Reservation :=
  if needsAllocation width data then
    Allocated.reservation s (SszNative.WordDecode.significantBytes data data.size)
  else none

def Observation (s t : ArmState) (width : Nat) (data : Ssz.Bytes) : Prop :=
  if needsAllocation width data then
    Allocated.Observation s t data (reservation s width data)
  else SszNative.UintCodec.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (Ssz.deserialize (.uint width) data)

/-- Full postdispatch body result. The resource branch, exact cursor, return
activation and permitted write footprint all refer to the original entry state. -/
structure Result (s t : ArmState) (width : Nat) (data : Ssz.Bytes) : Prop where
  returned : Allocated.Returned s t (SszNative.WordDecode.significantBytes data data.size)
    (reservation s width data)
  error : read_err t = .None
  observed : Observation s t width data
  cursor : Allocated.CursorAt s t (reservation s width data)

private theorem returned_of_nonallocating {s t : ArmState} (count : Nat)
    (hr : Tail.Returned s t) : Allocated.Returned s t count none := by
  refine ⟨hr.pc, hr.sp, hr.registers, hr.activation, ?_⟩
  intro a ho hw _
  exact hr.frame a (by simpa only [BitVec.ofNat_eq_ofNat] using ho)
    (by simpa only [BitVec.ofNat_eq_ofNat] using hw)

private theorem cursor_of_nonallocating {s t : ArmState} {data : Ssz.Bytes}
    (ho : Allocated.Owned s data) (hr : Tail.Returned s t) :
    Allocated.CursorAt s t none := by
  apply BoolCodec.read_bytes_congr
  intro i hi
  apply hr.frame
  · have hb := ho.headerHigh
    have hs := ho.headerOutput
    simp only [BitVec.ofNat_eq_ofNat] at *
    bv_omega
  · have hb := ho.headerHigh
    have hs := ho.headerStack
    simp only [BitVec.ofNat_eq_ofNat] at *
    bv_omega

/-- Every actual path from the UInt body entry reaches RET. Scope mismatch,
Small values, allocation exhaustion and arbitrarily many allocated limbs are
composed from checked instruction contracts without an execution premise. -/
theorem runs (s : ArmState) (base : BitVec 64) (width : Nat) (data : Ssz.Bytes)
    (hc : CodeAt s base) (hp : read_pc s = base + 148#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hheader : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64)
    (hspill : WidthScratchSeparated s) (hwidth : WidthPair s width)
    (hi : Small.Input s data) (ho : Allocated.Owned s data) :
    ∃ fuel t, run fuel s = t ∧ Result s t width data := by
  obtain ⟨fuel, t, hrun, hexit⟩ := prefix_finish_or_allocate s base width data
    hc hp he ha hheader hspill hwidth hi ho.tail
  rcases hexit with ⟨hnonalloc, hreturn, herror, hresult⟩ | hlarge
  · have hn : ¬ needsAllocation width data := by
      intro h
      rcases hnonalloc with hwidth | hcount
      · exact hwidth h.1
      · exact (Nat.not_lt_of_ge hcount) h.2
    refine ⟨fuel, t, hrun, ?_⟩
    refine ⟨?_, herror, ?_, ?_⟩
    · simpa only [reservation, hn, ↓reduceIte] using
        returned_of_nonallocating (SszNative.WordDecode.significantBytes data data.size) hreturn
    · simpa only [Observation, hn, ↓reduceIte] using hresult
    · simpa only [reservation, hn, ↓reduceIte] using cursor_of_nonallocating ho hreturn
  · obtain ⟨hmatch, hcount, hstable, hcode, herr, halign, hinput, hpc, h8, h9⟩ := hlarge
    have hn : needsAllocation width data := ⟨hmatch, hcount⟩
    obtain ⟨extra, u, hrun', hreturn, herror, hresult, hcursor⟩ :=
      allocated_body_runs t base data hcount hcode hpc herr halign hinput
        (ho.stable hstable) h8 h9
    have hreservation := ho.reservation_stable hstable
      (SszNative.WordDecode.significantBytes data data.size)
    rw [hreservation] at hreturn hresult hcursor
    have hout := hstable.regs 0 (by decide)
    refine ⟨fuel + extra, u, ?_, ?_⟩
    · rw [run_plus, hrun, hrun']
    · refine ⟨?_, herror, ?_, ?_⟩
      · simpa only [reservation, hn, ↓reduceIte] using hreturn.prepend ho hstable
      · simp only [Observation, reservation, hn, ↓reduceIte]
        simpa only [Allocated.Observation, hout] using hresult
      · simpa only [reservation, hn, ↓reduceIte] using hcursor.prepend ho hstable

/-- With enough resources for the path that actually allocates, the observed
result is precisely upstream UInt deserialization; scope errors need no arena. -/
theorem Result.refines {s t : ArmState} {width : Nat} {data : Ssz.Bytes}
    (h : Result s t width data)
    (hspace : needsAllocation width data →
      (Allocated.reservation s (SszNative.WordDecode.significantBytes data data.size)).isSome) :
    SszNative.UintCodec.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (Ssz.deserialize (.uint width) data) := by
  have ho := h.observed
  by_cases hn : needsAllocation width data
  · have hs := hspace hn
    cases hr : Allocated.reservation s (SszNative.WordDecode.significantBytes data data.size) with
    | none => simp only [hr, Option.isSome_none, Bool.false_eq_true] at hs
    | some q =>
      simp only [Observation, reservation, hn, ↓reduceIte, hr, Allocated.Observation] at ho
      apply SszNative.UintCodec.result_refines width data
      simpa only [SszNative.WordDecode.outcome, hn.1, ↓reduceIte,
        SszNative.WordDecode.decode_value, BitVec.ofNat_eq_ofNat] using ho
  · simpa only [Observation, hn, ↓reduceIte] using ho

end SszArm.UintCodec.Body
