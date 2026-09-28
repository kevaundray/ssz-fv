import SszArm.BitListReturn
import SszArm.BitVectorProgram

namespace SszArm.BitList

/-- All three actual linked images, with the shared comparison target relative
to decode_delimited rather than to the enclosing deserialize symbol. -/
structure JointCodeAt (s : ArmState) (base : BitVec 64) : Prop where
  body : CodeAt s base
  delimited : Delimited.CodeAt s (base + delimitedOffset)
  compare : NatCompare.CodeAt s (base + delimitedOffset + Delimited.compareOffset)

theorem JointCodeAt.run {s : ArmState} {base : BitVec 64}
    (code : JointCodeAt s base) (fuel : Nat) : JointCodeAt (run fuel s) base := by
  rcases code with ⟨body, delimited, compare⟩
  constructor
  · simpa only [CodeAt, BitVector.run_program] using body
  · simpa only [Delimited.CodeAt, BitVector.run_program] using delimited
  · simpa only [NatCompare.CodeAt, BitVector.run_program] using compare

theorem JointCodeAt.called {s : ArmState} {base : BitVec 64}
    (code : JointCodeAt s base) (kind : Variant) : JointCodeAt (called s base kind) base := by
  rcases code with ⟨body, delimited, compare⟩
  constructor
  · simpa only [CodeAt, called_program] using body
  · simpa only [Delimited.CodeAt, called_program] using delimited
  · simpa only [NatCompare.CodeAt, called_program] using compare

/-- Actual BitList entry2052 and ProgressiveBitList entry564 through the original
caller return. The only premises are original caller ownership, actual linked
code, and normal machine entry conditions. All semantic and resource branches
are handled by the complete shared decode_delimited proof. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (kind : Variant)
    (limit : Option Nat) (data : Ssz.Bytes) (owned : Owned s kind limit data)
    (code : JointCodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    ∃ fuel t, run fuel s = t ∧ Post s t kind limit data := by
  let entryFuel := match kind with | .list => 7 | .progressive => 10
  have entered : run entryFuel s = called s base kind := by
    cases kind with
    | list => exact list_entry_run s base code.body error aligned pc
    | progressive => exact progressive_entry_run s base code.body error aligned pc
  have helperCode := code.called kind
  obtain ⟨fuel, t, executed, post⟩ := Delimited.decode_correct (called s base kind)
    (base + delimitedOffset) limit data (helper_owned owned base) helperCode.delimited helperCode.compare
    (by simpa only [called_error] using error) (called_aligned s base kind aligned)
    (by
      change read_pc (called s base kind) = base + delimitedOffset + 0#64
      simpa only [BitVec.add_zero] using called_pc s base kind)
  have whole : run (entryFuel + fuel) s = t := by rw [run_plus, entered, executed]
  cases kind with
  | list =>
    have bodyCode : CodeAt t base := by
      rw [← whole]
      exact (code.run _).body
    have helperPC : read_pc t = base + 2080#64 := by
      simpa (config := {decide := true}) [called, listCalled, state_simp_rules] using post.returned.pc
    have helperAligned : CheckSPAlignment t := by
      have sp : r (.GPR 31#5) t = r (.GPR 31#5) s := by
        simpa only [called_sp, helperSP] using post.returned.sp
      simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, sp] using aligned
    have returnedRun := return_run t base bodyCode post.returned.error helperAligned helperPC
    refine ⟨entryFuel + fuel + 9, BoolCodec.returned t, ?_, ?_⟩
    · rw [run_plus, whole, returnedRun]
    · exact post_of_helper owned post (BoolCodec.returned_mem t) (list_returned owned post)
  | progressive =>
    exact ⟨entryFuel + fuel, t, whole, post_of_helper owned post rfl (progressive_returned post)⟩

/-- BitList imposes Some(cap), without canonicality or machine-word bounds on cap. -/
theorem bitList_correct (s : ArmState) (base : BitVec 64) (capacity : Nat) (data : Ssz.Bytes)
    (owned : Owned s .list (some capacity) data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 listEntry) :
    ∃ fuel t, run fuel s = t ∧ Post s t .list (some capacity) data :=
  program_correct s base .list (some capacity) data owned code error aligned pc

/-- The tail entry supports both None and arbitrarily represented Some(cap). -/
theorem progressiveBitList_correct (s : ArmState) (base : BitVec 64) (limit : Option Nat) (data : Ssz.Bytes)
    (owned : Owned s .progressive limit data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 progressiveEntry) :
    ∃ fuel t, run fuel s = t ∧ Post s t .progressive limit data :=
  program_correct s base .progressive limit data owned code error aligned pc

/-- Resource failure is distinct from the pinned SSZ semantic result. -/
theorem Post.refines {s t : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (post : Post s t kind limit data) :
    if SszNative.Delimited.Exhausted data (arenaOf s) then
      SszNative.UintCodec.errorAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
    else SszNative.BitView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
      (Ssz.deserialize (.progressiveBitList limit) data) := by
  by_cases exhausted : SszNative.Delimited.Exhausted data (arenaOf s)
  · simp only [exhausted, ↓reduceIte]
    have result := (SszNative.Delimited.run_scratch_iff limit data (arenaOf s) owned.physical).mpr exhausted
    simpa only [outcome, SszNative.Delimited.ResultAt, result] using post.result
  · simp only [exhausted, ↓reduceIte]
    rw [← SszNative.BitView.progressive_outcome_eq_deserialize limit data]
    exact SszNative.Delimited.result_refines _ _ _ _ limit data (arenaOf s)
      owned.physical exhausted post.result

theorem Post.bitList {s t : ArmState} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s .list (some capacity) data) (post : Post s t .list (some capacity) data) :
    if SszNative.Delimited.Exhausted data (arenaOf s) then
      SszNative.UintCodec.errorAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
    else SszNative.BitView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
      (Ssz.deserialize (.bitList capacity) data) := by
  simpa only [← SszNative.BitView.progressive_outcome_eq_deserialize,
    SszNative.BitView.list_outcome_eq_deserialize] using post.refines owned

/-- Pinned bounded SSZ corollary, retaining the entire native resource/ABI post. -/
theorem bitList_ssz_correct (s : ArmState) (base : BitVec 64) (capacity : Nat) (data : Ssz.Bytes)
    (owned : Owned s .list (some capacity) data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 listEntry) :
    ∃ fuel t, run fuel s = t ∧ Post s t .list (some capacity) data ∧
      (if SszNative.Delimited.Exhausted data (arenaOf s) then
        SszNative.UintCodec.errorAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
      else SszNative.BitView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.bitList capacity) data)) := by
  obtain ⟨fuel, t, executed, post⟩ := bitList_correct s base capacity data owned code error aligned pc
  exact ⟨fuel, t, executed, post, post.bitList owned⟩

/-- Pinned progressive SSZ corollary for both optional-cap cases. -/
theorem progressiveBitList_ssz_correct (s : ArmState) (base : BitVec 64) (limit : Option Nat) (data : Ssz.Bytes)
    (owned : Owned s .progressive limit data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 progressiveEntry) :
    ∃ fuel t, run fuel s = t ∧ Post s t .progressive limit data ∧
      (if SszNative.Delimited.Exhausted data (arenaOf s) then
        SszNative.UintCodec.errorAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
      else SszNative.BitView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.progressiveBitList limit) data)) := by
  obtain ⟨fuel, t, executed, post⟩ := progressiveBitList_correct s base limit data owned code error aligned pc
  exact ⟨fuel, t, executed, post, post.refines owned⟩

end SszArm.BitList
