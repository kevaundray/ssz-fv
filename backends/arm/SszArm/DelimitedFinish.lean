import SszArm.DelimitedPrepared
import SszArm.DelimitedTails

namespace SszArm.Delimited

open UintCodec (widthLoad)
open UintCodec.Tail (write_pair_words)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem finish_model {s u : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (state : Ready s u base limit data ready) (nonempty : 0 < data.size)
    (delimiter : data[data.size - 1]! ≠ 0) :
    SszNative.Delimited.run limit data (arenaOf s) =
      SszNative.Delimited.finish limit data.size (Ssz.highestBit data[data.size - 1]!) ready := by
  rw [SszNative.Delimited.run_valid _ _ _ nonempty delimiter, state.prepared]

/-- The write footprint is rooted in the original entry, independently of the
intermediate state from which a terminal block executes. -/
theorem finish_lift_frame {s u t : ArmState}
    (allocation : Option SszNative.Arena.Reservation)
    (frame : MemoryFrame (localWrites s) u t) : MemoryFrame (writesFor s allocation) u t := by
  apply frame.weaken
  intro span member
  cases allocation <;> simp_all [writesFor, allocatedWrites]

theorem finish_fresh {s u : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (owned : Owned s limit data) (state : Ready s u base limit data ready)
    (reservation : SszNative.Arena.Reservation) (allocated : ready.allocation = some reservation) :
    Protected (localWrites s) reservation.pointer 16 ∧ reservation.pointer + 16 ≤ 2^64 := by
  have allocation := state.allocation.trans allocated
  have reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
      (arenaOf s).used 2 = some reservation := by
    unfold SszNative.Delimited.allocation at allocation
    split at allocation
    · exact allocation
    · contradiction
  have geometry := SszNative.Delimited.reservation_bounds _ _ _ owned.arenaStorage
    owned.arenaNonnull reservation reserved
  refine ⟨?_, geometry.2.2.2.2.2⟩
  rcases owned.fresh reservation (state.allocation.trans allocated) with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    exact separate span (List.mem_append_left _ member)

theorem finish_local_protected {s : ArmState}
    {allocation : Option SszNative.Arena.Reservation} {address bytes : Nat}
    (separation : Protected (writesFor s allocation) address bytes) :
    Protected (localWrites s) address bytes := by
  rcases separation with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    apply separate span
    cases allocation <;> simp_all [writesFor, allocatedWrites]

theorem finish_tail_protected {s u : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data) (nonempty : r (.GPR 3#5) s ≠ 0#64)
    (out : r (.GPR 0#5) u = r (.GPR 0#5) s)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64)
    {address bytes : Nat} (separation : Protected (localWrites s) address bytes) :
    Protected (tailWrites u) address bytes := by
  have stack := owned.stackBound
  simp only [activationSpan, nonempty, ↓reduceIte] at stack
  have spNat : (r (.GPR 31#5) u).toNat = (r (.GPR 31#5) s).toNat - 96 := by bv_omega
  rcases separation with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    simp only [tailWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simpa only [out] using separate ((r (.GPR 0#5) s).toNat, 76) (by simp [localWrites])
    · have apart := separate (activationSpan s) (by simp [localWrites])
      simp only [activationSpan, nonempty, ↓reduceIte] at apart
      simp only [spNat]
      omega

/-- The constructed actual count may borrow its freshly reserved limbs. Those
sixteen bytes are disjoint from precisely the writes made by returning tails. -/
theorem Ready.actual_owned {s u : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (state : Ready s u base limit data ready) (owned : Owned s limit data)
    (nonempty : 0 < data.size) :
    NatOwned (tailWrites u) (r (.GPR 20#5) u) (r (.GPR 19#5) u) := by
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by have h := owned.length; bv_omega
  have out := state.arguments 0#5 (by simp)
  have sp := state.saved.sp
  rw [state.pointer, state.payload]
  cases allocated : ready.allocation with
  | none => simp [SszNative.Delimited.Prepared.pointer, allocated, NatOwned]
  | some reservation =>
    have fresh := finish_fresh owned state reservation allocated
    have ptrBound : reservation.pointer < 2^64 := by omega
    simp only [SszNative.Delimited.Prepared.pointer, SszNative.Delimited.Prepared.payload, allocated]
    intro _ _
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound] using
      finish_tail_protected owned nonzero out sp fresh.1

theorem finish_stored {s u t : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (owned : Owned s limit data) (state : Ready s u base limit data ready)
    (frame : MemoryFrame (localWrites s) u t) : SszNative.Delimited.PreparedAt (widthLoad t) ready := by
  have stored := state.stored
  cases allocated : ready.allocation with
  | none => simpa only [SszNative.Delimited.PreparedAt, allocated] using stored
  | some reservation =>
    have fresh := finish_fresh owned state reservation allocated
    simp only [SszNative.Delimited.PreparedAt, allocated] at stored ⊢
    rw [frame.load reservation.pointer 8 (by omega)
      (by simpa using fresh.1.subspan 0 8 (by decide)),
      frame.load (reservation.pointer + 8) 8 (by omega) (fresh.1.subspan 8 8 (by decide))]
    exact stored

/-- A returning tail cannot roll back the count reservation, alter its limbs,
or change the caller's cursor. Only its actual local output/lowering writes
are composed with the already-checked prepare/compare frame. -/
private theorem finish_post {s u t : ArmState} {base : BitVec 64} {limit : Option Nat}
    {data : Ssz.Bytes} {ready : SszNative.Delimited.Prepared}
    (owned : Owned s limit data) (state : Ready s u base limit data ready)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (returned : Returned s t) (frame : MemoryFrame (localWrites s) u t)
    (result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat (r (.GPR 1#5) s).toNat data
      (SszNative.Delimited.run limit data (arenaOf s))) : Post s t limit data := by
  have model := finish_model state nonempty delimiter
  have allFrame := state.frame.trans (finish_lift_frame ready.allocation frame)
  apply post_of_frame s t limit data owned returned result
  · rw [model]
    intro other equal
    have same : ready = other := Option.some.inj equal
    subst other
    exact finish_stored owned state frame
  · have same := Option.some.inj (frame.load ((r (.GPR 4#5) s).toNat + 16) 8
      (by have h := owned.arenaBound; omega) (owned.arenaLocal.subspan 16 8 (by decide)))
    have cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = ready.used := by
      have same' : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
          (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) u).toNat := by
        simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using same
      exact same'.trans state.cursor
    simpa only [model, SszNative.Delimited.finish] using cursor
  · simpa only [model, SszNative.Delimited.finish, SszNative.Delimited.Outcome.allocation,
      Option.bind_some] using allFrame

/-- Complete success from the real p540 check. The shared result observes the
full original input, while the output retains exactly its native borrowed
pointer, byte count, and two count limbs. -/
theorem success_finish (s u : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (ready : SszNative.Delimited.Prepared)
    (owned : Owned s limit data) (state : Ready s u base limit data ready)
    (hc : CodeAt s base) (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (hp : read_pc u = base + 540#64)
    (bounded : ∀ cap, limit = some cap → ready.count.value ≤ cap) :
    ∃ fuel t, run fuel u = t ∧ Post s t limit data := by
  let highest := Ssz.highestBit data[data.size - 1]!
  let v := representationState base highest u
  let t := tailResult .success base v
  have bit : highest < 8 := SszNative.BitView.highestBit_lt _
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by have h := owned.length; bv_omega
  have code : CodeAt u base := by simpa only [CodeAt, state.program] using hc
  have lenReg : r (.GPR 3#5) u = BitVec.ofNat 64 data.size := by
    rw [state.arguments 3#5 (by simp), ← owned.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have clzReg : (r (.GPR 26#5) u).setWidth 32 = BitVec.ofNat 32 (7 - highest) := by
    rw [state.counter]
    bv_omega
  have values := representation_values u base data.size highest nonempty owned.physical bit
    lenReg state.preceding clzReg
  have registers := representation_register u base highest
  have out : r (.GPR 0#5) v = r (.GPR 0#5) s :=
    (registers _ (by decide) (by decide) (by decide)).trans (state.arguments _ (by simp))
  have pointer : r (.GPR 2#5) v = r (.GPR 2#5) s :=
    (registers _ (by decide) (by decide) (by decide)).trans (state.arguments _ (by simp))
  have spU : r (.GPR 31#5) v = r (.GPR 31#5) u := registers _ (by decide) (by decide) (by decide)
  have sp := spU.trans state.saved.sp
  have memory : v.mem = u.mem := representation_memory u base highest
  have saved : Saved s v := by
    refine ⟨sp, ?_, ?_⟩
    · intro reg offset member
      rw [spU, (Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) 8]
      exact state.saved.words reg offset member
    · intro reg low high
      rw [show r (.SFP reg) v = r (.SFP reg) u from representation_vectors u base highest reg]
      exact state.saved.vectors reg low high
  have ownership := owned.tail_owned nonzero out sp
  have exec := tail_run_returned .success s v base
    (by simpa only [v, representationState, CodeAt, block_program] using code)
    (by simpa only [v, representationState, block_error] using state.error)
    (block_aligned base (representationOps highest) u state.aligned) values.1 saved ownership
  have localFrame : MemoryFrame (localWrites s) u t := by
    have checkFrame : MemoryFrame (localWrites s) u v := fun a _ => congrFun memory a
    exact checkFrame.trans (tail_frame_local owned nonzero out sp (tailMemoryFrame .success v base ownership))
  have allFrame := state.frame.trans (finish_lift_frame ready.allocation localFrame)
  have inputs := inputs_preserved owned (by simpa only [state.allocation] using allFrame)
  have lowWord : r (.GPR 24#5) v = BitVec.ofNat 64 ready.count.value := by
    rw [registers _ (by decide) (by decide) (by decide), state.low]
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ofNat] using ready.count.parts.2.1.symm
  have highWord : r (.GPR 23#5) v = BitVec.ofNat 64 (ready.count.value / 2^64) := by
    rw [registers _ (by decide) (by decide) (by decide), state.high,
      ready.count.parts.2.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have image := success_tail_memory v base (SszNative.Delimited.retainedBytes data.size highest)
    ready.count.value values.2.2 lowWord highWord values.2.1
  have loads : widthLoad t = widthLoad (successMemory v (r (.GPR 0#5) v)
      (r (.GPR 2#5) v) (SszNative.Delimited.retainedBytes data.size highest) ready.count.value) := by
    funext a n
    unfold widthLoad
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp image) n]
  have byteBound : SszNative.Delimited.retainedBytes data.size highest < 2^64 := by
    have bound := owned.physical
    unfold SszNative.Delimited.retainedBytes
    split <;> omega
  have outputBound : (r (.GPR 0#5) v).toNat + 76 ≤ 2^64 := by simpa only [out] using owned.outputBound
  have lowNat := ready.count.parts.2.1
  have highNat := ready.count.parts.2.2
  have result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat (r (.GPR 1#5) s).toNat data
      (SszNative.Delimited.run limit data (arenaOf s)) := by
    rw [finish_model state nonempty delimiter]
    change SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat (r (.GPR 1#5) s).toNat data
      (SszNative.Delimited.finish limit data.size highest ready)
    have outcome : SszNative.Delimited.finish limit data.size highest ready =
        ⟨.ok ⟨0, SszNative.Delimited.retainedBytes data.size highest, ready.count⟩,
          ready.used, some ready⟩ := by
      cases limit with
      | none => rfl
      | some cap => simp only [SszNative.Delimited.finish, bounded cap rfl, ↓reduceIte]
    rw [outcome]
    simp only [SszNative.Delimited.ResultAt, Nat.add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, inputs.input⟩
    all_goals
      rw [loads]
      simp only [← out, ← pointer, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
      simp (disch := delimited_side) [successMemory, write_pair_words, BitVec.add_assoc,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt byteBound, lowNat, highNat]
  refine ⟨(representationOps highest).length + 13, t, ?_,
    finish_post owned state nonempty delimiter exec.2 localFrame result⟩
  rw [run_plus, representation_run u base data.size highest code state.error state.aligned hp
    nonempty owned.physical bit lenReg state.preceding clzReg]
  exact exec.1

/-- Over-limit rejection preserves the exact original optional-cap descriptor,
and the actual newly prepared Small/Large descriptor, through the real RET. -/
theorem over_limit_finish (s u : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (ready : SszNative.Delimited.Prepared) (cap : Nat)
    (owned : Owned s limit data) (state : Ready s u base limit data ready)
    (hc : CodeAt s base) (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (limitEq : limit = some cap) (exceeded : cap < ready.count.value)
    (hp : read_pc u = base + 424#64)
    (expectedPointer : r (.GPR 22#5) u = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
    (expectedPayload : r (.GPR 21#5) u = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s) :
    ∃ t, run 53 u = t ∧ Post s t limit data := by
  subst limit
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by have h := owned.length; bv_omega
  have out := state.arguments 0#5 (by simp)
  have sp := state.saved.sp
  have ownership := owned.tail_owned nonzero out sp
  have code : CodeAt u base := by simpa only [CodeAt, state.program] using hc
  let t := tailResult .overLimit base u
  have exec := tail_run_returned .overLimit s u base code state.error state.aligned hp state.saved ownership
  have localFrame := tail_frame_local owned nonzero out sp (tailMemoryFrame .overLimit u base ownership)
  have allFrame := state.frame.trans (finish_lift_frame ready.allocation localFrame)
  have header : Protected (writesFor s ready.allocation) (r (.GPR 1#5) s).toNat 24 := by
    simpa only [state.allocation] using owned.optionOwned.1
  have currentPointer : widthLoad u ((r (.GPR 1#5) s).toNat + 8) 8 =
      some (r (.GPR 22#5) u).toNat := by
    rw [state.frame.load _ _ (by have h := owned.optionBound; omega) (header.subspan 8 8 (by decide))]
    simp [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, expectedPointer]
  have currentPayload : widthLoad u ((r (.GPR 1#5) s).toNat + 8 + 8) 8 =
      some (r (.GPR 21#5) u).toNat := by
    have same := state.frame.load ((r (.GPR 1#5) s).toNat + 16) 8
      (by have h := owned.optionBound; omega) (header.subspan 16 8 (by decide))
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, expectedPayload,
      Nat.add_assoc, BitVec.add_assoc] using same
  have expectedPair := SszNative.NatMemory.pair_of_at _ _ _ cap _
    (state.inputs owned).option.2 currentPointer currentPayload
  have expectedOwned : NatOwned (tailWrites u) (r (.GPR 22#5) u) (r (.GPR 21#5) u) := by
    rw [expectedPointer, expectedPayload]
    intro positive nonemptyWords
    exact finish_tail_protected owned nonzero out sp
      (finish_local_protected (owned.optionOwned.2 positive nonemptyWords))
  have actualOwned := state.actual_owned owned nonempty
  have image := over_limit_tail_image u base cap ready.count.value ownership
    expectedPair (state.pair owned) expectedOwned actualOwned
  have fields := over_limit_tail_fields u base ownership
  have finalPointer : widthLoad t ((r (.GPR 1#5) s).toNat + 8) 8 =
      some (r (.GPR 22#5) u).toNat := by
    rw [allFrame.load _ _ (by have h := owned.optionBound; omega) (header.subspan 8 8 (by decide))]
    simp [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, expectedPointer]
  have finalPayload : widthLoad t ((r (.GPR 1#5) s).toNat + 16) 8 =
      some (r (.GPR 21#5) u).toNat := by
    rw [allFrame.load _ _ (by have h := owned.optionBound; omega) (header.subspan 16 8 (by decide))]
    simp [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, expectedPayload]
  have descriptorBounds : ready.pointer < 2^64 ∧ ready.payload < 2^64 := by
    cases allocated : ready.allocation with
    | none => simpa [SszNative.Delimited.Prepared.pointer, SszNative.Delimited.Prepared.payload, allocated] using
        (show 0 < 2^64 ∧ ready.count.low.toNat < 2^64 from ⟨by decide, ready.count.low.isLt⟩)
    | some reservation =>
      have fresh := finish_fresh owned state reservation allocated
      simp only [SszNative.Delimited.Prepared.pointer, SszNative.Delimited.Prepared.payload, allocated]
      constructor <;> omega
  have result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat (r (.GPR 1#5) s).toNat data
      (SszNative.Delimited.run (some cap) data (arenaOf s)) := by
    rw [finish_model state nonempty delimiter]
    simp only [SszNative.Delimited.finish, Nat.not_le.mpr exceeded, ↓reduceIte,
      SszNative.Delimited.ResultAt]
    rw [out] at image fields
    refine ⟨image, fields.1.trans finalPointer.symm, fields.2.1.trans finalPayload.symm,
      ready, rfl, ?_, ?_⟩
    · simpa only [state.pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt descriptorBounds.1] using fields.2.2.1
    · simpa only [state.payload, BitVec.toNat_ofNat, Nat.mod_eq_of_lt descriptorBounds.2] using fields.2.2.2
  exact ⟨t, exec.1, finish_post owned state nonempty delimiter exec.2 localFrame result⟩

end SszArm.Delimited
