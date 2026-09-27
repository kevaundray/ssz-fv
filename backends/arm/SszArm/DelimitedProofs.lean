import SszArm.DelimitedComparePhase
import SszArm.DelimitedSmallPhase
import SszArm.DelimitedReservePhase

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem ready_finish (s u : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (ready : SszNative.Delimited.Prepared)
    (owned : Owned s limit data) (state : Ready s u base limit data ready)
    (hc : CodeAt s base) (compareCode : NatCompare.CodeAt s (base + compareOffset))
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (optionAddress : r (.GPR 1#5) u = r (.GPR 1#5) s)
    (hp : read_pc u = if limit.isSome then base + 364#64 else base + 540#64) :
    ∃ fuel t, run fuel u = t ∧ Post s t limit data := by
  cases limit with
  | none =>
    exact success_finish s u base none data ready owned state hc nonempty delimiter
      (by simpa using hp) (by intro cap impossible; cases impossible)
  | some cap =>
    obtain ⟨fuel, v, called, compared, pcV, expectedPointer, expectedPayload⟩ :=
      compare_ready s u base cap data ready owned state hc compareCode nonempty
        (by simpa using hp) optionAddress
    by_cases exceeded : cap < ready.count.value
    · have order : compare ready.count.value cap = .gt := Nat.compare_eq_gt.mpr exceeded
      obtain ⟨t, finished, post⟩ := over_limit_finish s v base (some cap) data ready cap
        owned compared hc nonempty delimiter rfl exceeded
        (by simpa only [order, ↓reduceIte] using pcV) expectedPointer expectedPayload
      refine ⟨fuel + 53, t, ?_, post⟩
      rw [run_plus, called, finished]
    · have order : compare ready.count.value cap ≠ .gt :=
        fun greater => exceeded (Nat.compare_eq_gt.mp greater)
      obtain ⟨tailFuel, t, finished, post⟩ := success_finish s v base (some cap) data ready
        owned compared hc nonempty delimiter (by simpa only [order, ↓reduceIte] using pcV)
        (by intro other equal; cases equal; exact Nat.le_of_not_gt exceeded)
      refine ⟨fuel + tailFuel, t, ?_, post⟩
      rw [run_plus, called, finished]

/-- Complete execution of the bound decode_delimited image from its actual
entry through its actual RET, including the sole linked Nat.compare callee.

Only instruction images and caller-owned physical memory are premises. The
postcondition observes the shared native model, exact scratch cursor/words,
original readonly data and optional-cap representation, output and activation
frame, and return-address/SP/callee-saved restoration. In particular, no
execution, codec-correctness, Nat-ordering, signed-length, or canonical-cap
hypothesis is assumed. This theorem does not claim the outer dispatch wrappers. -/
theorem decode_correct (s : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (owned : Owned s limit data)
    (hc : CodeAt s base) (compareCode : NatCompare.CodeAt s (base + compareOffset))
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ fuel t, run fuel s = t ∧ Post s t limit data := by
  by_cases empty : data.size = 0
  · obtain ⟨t, executed, post⟩ := empty_model_correct s base limit data owned hc he ha hp empty
    exact ⟨19, t, executed, post⟩
  have nonempty : 0 < data.size := Nat.pos_of_ne_zero empty
  by_cases delimiter : data[data.size - 1]! = 0
  · exact invalid_model_correct s base limit data owned hc he ha hp nonempty delimiter
  obtain ⟨u, startedRun, started⟩ := nonempty_start s base limit data owned hc he ha hp nonempty
  obtain ⟨v, countedRun, counted⟩ := count_phase s u base limit data owned started hc nonempty delimiter
  have continued : ∃ fuel t, run fuel v = t ∧ Post s t limit data := by
    by_cases small :
        (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high = 0#64
    · obtain ⟨ready, w, preparedRun, prepared, optionAddress, pcW⟩ :=
        small_prepare s v base limit data owned counted hc nonempty delimiter small
      obtain ⟨fuel, t, finished, post⟩ := ready_finish s w base limit data ready owned prepared
        hc compareCode nonempty delimiter optionAddress pcW
      refine ⟨(if limit.isSome then 5 else 6) + fuel, t, ?_, post⟩
      rw [run_plus, preparedRun, finished]
    · rcases large_reservation_phase s v base limit data owned counted hc nonempty delimiter small with
        exhausted | prepared
      · exact exhausted
      · obtain ⟨fuel, w, ready, preparedRun, state, optionAddress, pcW⟩ := prepared
        obtain ⟨tailFuel, t, finished, post⟩ := ready_finish s w base limit data ready owned state
          hc compareCode nonempty delimiter optionAddress pcW
        refine ⟨fuel + tailFuel, t, ?_, post⟩
        rw [run_plus, preparedRun, finished]
  obtain ⟨fuel, t, finished, post⟩ := continued
  refine ⟨16 + (10 + 3 * (25 + Ssz.highestBit data[data.size - 1]!) + 8) + fuel, t, ?_, post⟩
  rw [run_plus, run_plus, startedRun, countedRun, finished]

/-- Pinned SSZ semantics, with the native scratch failure kept explicit. Both
bounded BitList and ProgressiveBitList use this delimited result relation. -/
theorem Post.refines {s t : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data) (post : Post s t limit data) :
    if SszNative.Delimited.Exhausted data (arenaOf s) then
      SszNative.UintCodec.errorAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
    else
      SszNative.BitView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.progressiveBitList limit) data) := by
  by_cases exhausted : SszNative.Delimited.Exhausted data (arenaOf s)
  · simp only [exhausted, ↓reduceIte]
    have result := (SszNative.Delimited.run_scratch_iff limit data (arenaOf s)
      owned.physical).mpr exhausted
    simpa only [SszNative.Delimited.ResultAt, result] using post.result
  · simp only [exhausted, ↓reduceIte]
    rw [← SszNative.BitView.progressive_outcome_eq_deserialize limit data]
    exact SszNative.Delimited.result_refines _ _ _ _ limit data (arenaOf s)
      owned.physical exhausted post.result

theorem Post.bitList {s t : ArmState} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s (some capacity) data) (post : Post s t (some capacity) data) :
    if SszNative.Delimited.Exhausted data (arenaOf s) then
      SszNative.UintCodec.errorAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat 32768 0 0
    else
      SszNative.BitView.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.bitList capacity) data) := by
  simpa only [← SszNative.BitView.progressive_outcome_eq_deserialize,
    SszNative.BitView.list_outcome_eq_deserialize] using post.refines owned

end SszArm.Delimited
