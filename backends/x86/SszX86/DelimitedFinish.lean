import SszX86.DelimitedFinishMemory
import SszX86.DelimitedRetain

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem return_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 88)
    (simd : t.zmms = s.zmms) (hm : OutputMapped t)
    (saved : SavedAt t.dmem t.regs.rsp.toBitVec s)
    (observed : SszNative.Delimited.ResultAt (widthLoad (tagged t).dmem)
      s.regs.rdi.toNat s.regs.rdx.toNat s.regs.rsi.toNat data
      (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩))
    (prepared : SszNative.Delimited.Outcome.PreparedAt (widthLoad (tagged t).dmem)
      (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩))
    (frame : Frame s (tagged t).dmem data
      (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation)
    (cursor : widthLoad (tagged t).dmem (s.regs.r8.toNat + 16) 8 =
      some (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).used)
    (P : MachineState → Prop)
    (hp : ∀ u, Post s limit data address capacity used ra u → P u) :
    Eventually (step e) P (t, base + 823) := by
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
  have resources := (SszNative.Delimited.run_resources limit data
    ⟨address.toNat, capacity.toNat, used.toNat⟩ physical).1
  have returnLoad := frame_return_load s limit data address capacity used ra h
    (tagged t).dmem (by simpa only [resources] using frame)
  apply restore_cps e base hc t s saved P
  intro flags
  apply tag_cps e base hc (restoredState t s flags) hm P
  have post : Post s limit data address capacity used ra
      (retState (tagged (restoredState t s flags)), Int64.ofBitVec ra) := by
    refine ⟨observed, prepared, ?_, frame, cursor⟩
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, simd, returnLoad⟩
    simp only [retState, tagged, restoredState, UInt64.toBitVec_ofBitVec, sp]
    bv_omega
  apply (ret_runs e base hc (tagged (restoredState t s flags)) ra P ?_ (hp _ post)).2.2
  simpa only [tagged, restoredState, UInt64.toBitVec_ofBitVec, sp,
    BitVec.sub_add_cancel] using returnLoad

private theorem ready_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t u : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (ready : SszNative.Delimited.Prepared)
    (state : Ready s t limit data address capacity used ready)
    (sp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec)
    (simd : u.zmms = t.zmms) (hm : OutputMapped u)
    (saved : SavedAt u.dmem u.regs.rsp.toBitVec s)
    (written : ∀ a : BitVec 64, (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      (tagged u).dmem.get? a = t.dmem.get? a)
    (observed : SszNative.Delimited.ResultAt (widthLoad (tagged u).dmem)
      s.regs.rdi.toNat s.regs.rdx.toNat s.regs.rsi.toNat data
      (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩))
    (P : MachineState → Prop)
    (hp : ∀ v, Post s limit data address capacity used ra v → P v) :
    Eventually (step e) P (u, base + 823) := by
  have model := state.model nonempty delimiter
  apply return_tail_cps e base hc s u limit data address capacity used ra h
    (sp.trans state.active.sp) (simd.trans state.active.simd) hm saved observed
  · rw [model]
    intro other equal
    have same : ready = other := Option.some.inj equal
    subst other
    exact state.stored_output h (tagged u).dmem written
  · simpa only [model, SszNative.Delimited.finish, SszNative.Delimited.Outcome.allocation,
      Option.bind_some] using frame_output s t.dmem (tagged u).dmem data ready.allocation
        h.output_bound state.frame written
  · simpa only [model, SszNative.Delimited.finish] using state.cursor_output h (tagged u).dmem written
  · exact hp

private theorem ready_word_bounds {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (h : Owned s limit data address capacity used ra)
    (state : Ready s t limit data address capacity used ready) :
    ready.pointer < 2^64 ∧ ready.payload < 2^64 := by
  cases allocation : ready.allocation with
  | none =>
    simp only [SszNative.Delimited.Prepared.pointer, SszNative.Delimited.Prepared.payload, allocation]
    exact ⟨by decide, ready.count.low.isLt⟩
  | some reservation =>
    have bounds := allocation_bounds s limit data address capacity used ra h reservation
      (state.allocation.trans allocation)
    simp only [SszNative.Delimited.Prepared.pointer, SszNative.Delimited.Prepared.payload, allocation]
    exact ⟨by omega, by decide⟩

/-- The retained-length guards, actual success stores, saved-register pops,
result tag, and RET establish the complete shared-model postcondition. -/
theorem success_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (ready : SszNative.Delimited.Prepared)
    (state : Ready s t limit data address capacity used ready)
    (bounded : ∀ cap, limit = some cap → ready.count.value ≤ cap)
    (P : MachineState → Prop)
    (hp : ∀ u, Post s limit data address capacity used ra u → P u) :
    Eventually (step e) P (t, base + 523) := by
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
  have retained : SszNative.Delimited.retainedBytes data.size
      (Ssz.highestBit data[data.size - 1]!) < 2^64 := by
    unfold SszNative.Delimited.retainedBytes
    split <;> omega
  have model := state.model nonempty delimiter
  have success : SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
      ⟨.ok ⟨0, SszNative.Delimited.retainedBytes data.size
        (Ssz.highestBit data[data.size - 1]!), ready.count⟩, ready.used, some ready⟩ := by
    rw [model]
    cases limit with
    | none => rfl
    | some cap => simp only [SszNative.Delimited.finish, bounded cap rfl, ↓reduceIte]
  apply retain_prepare_cps e base hc t data.size (Ssz.highestBit data[data.size - 1]!)
    (SszNative.BitView.highestBit_lt _) state.active.length state.active.preceding state.active.highest P
  intro prepareFlags
  apply retain_add_cps e base hc
    (retainPrepared t data.size (Ssz.highestBit data[data.size - 1]!) prepareFlags)
    data.size (Ssz.highestBit data[data.size - 1]!)
    nonempty physical (by exact state.active.preceding) rfl rfl P
  intro addFlags
  apply retain_check_cps e base hc _ rfl rfl P
  intro checkFlags
  let v := {retainAdded (retainPrepared t data.size (Ssz.highestBit data[data.size - 1]!) prepareFlags)
      (SszNative.Delimited.retainedBytes data.size (Ssz.highestBit data[data.size - 1]!)) addFlags with
    regs := {(retainAdded (retainPrepared t data.size (Ssz.highestBit data[data.size - 1]!) prepareFlags)
      (SszNative.Delimited.retainedBytes data.size (Ssz.highestBit data[data.size - 1]!)) addFlags).regs with rax := 0}
    status := checkFlags}
  change Eventually (step e) P (v, base + 555)
  apply success_stores_cps e base hc v state.active.output P
  intro flags
  have out : v.regs.rdi = s.regs.rdi := state.active.out
  have written : ∀ a : BitVec 64,
      (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      (tagged (successReady v flags)).dmem.get? a = t.dmem.get? a := by
    intro a outside
    exact success_frame v flags a (by simpa only [out] using outside)
  have untagged : ∀ a : BitVec 64,
      (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      (successReady v flags).dmem.get? a = t.dmem.get? a := by
    intro a outside
    have outside' : ∀ i < 76, a ≠ v.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
      simpa only [out] using outside
    simp (disch := first | exact outside' | omega | decide) only
      [successReady, successMem, BoolCodec.store_frame (limit := 76)]
    rfl
  have finalFrame := frame_output s t.dmem (tagged (successReady v flags)).dmem data
    ready.allocation h.output_bound state.frame written
  apply ready_tail_cps e base hc s t (successReady v flags) limit data address capacity used ra h
    nonempty delimiter ready state rfl rfl
  · change Large.Mapped (successMem v) v.regs.rdi.toBitVec 76
    unfold successMem
    repeat' first | exact state.active.output | apply Large.mapped_store
  · exact savedAt_output s limit data address capacity used ra h ⟨nonempty, delimiter⟩
      t.dmem _ t.regs.rsp.toBitVec state.active.sp state.active.saved untagged
  · exact written
  · rw [success]
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    have fields := success_fields v flags (by simpa only [out] using h.output_bound)
    have low : v.regs.r14.toNat = ready.count.low.toNat := congrArg BitVec.toNat state.low
    have high : v.regs.rbp.toNat = ready.count.high.toNat := congrArg BitVec.toNat state.high
    have count : v.regs.rcx.toNat = SszNative.Delimited.retainedBytes data.size
        (Ssz.highestBit data[data.size - 1]!) := by
      change (UInt64.ofNat _).toNat = _
      simp only [← UInt64.toNat_toBitVec, UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt retained]
    have source : v.regs.rdx = s.regs.rdx := state.active.source
    obtain ⟨tag, kind, pointer, bytes, lo, hi⟩ := fields
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [out] using tag
    · simpa only [out] using kind
    · simpa only [out, source, Nat.add_zero] using pointer
    · simpa only [out, count] using bytes
    · simpa only [out, low] using lo
    · simpa only [out, high] using hi
    · exact frame_source s limit data address capacity used ra h _
        (by simpa only [state.allocation] using finalFrame)
  · exact hp

/-- Reservation failure writes ScratchExhausted32768, restores the caller, and
executes the real RET without changing the original arena cursor. -/
theorem scratch_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (active : Active s t data) (frame : Frame s t.dmem data none)
    (cursor : widthLoad t.dmem (s.regs.r8.toNat + 16) 8 = some used.toNat)
    (model : SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
      ⟨.error .scratchExhausted, used.toNat, none⟩)
    (P : MachineState → Prop)
    (hp : ∀ u, Post s limit data address capacity used ra u → P u) :
    Eventually (step e) P (t, base + 736) := by
  apply scratch_stores_cps e base hc t active.output P
  intro flags
  apply error_tail_cps e base hc (scratchReady t flags)
  · change Large.Mapped (scratchMem t) t.regs.rdi.toBitVec 76
    unfold scratchMem
    repeat' first | exact active.output | apply Large.mapped_store
  · change 8 + 8 ≤ (76 : Nat)
    decide
  · change 16 + 8 ≤ (76 : Nat)
    decide
  have written : ∀ a : BitVec 64,
      (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      (tagged (errorTailReady (scratchReady t flags))).dmem.get? a = t.dmem.get? a := by
    intro a outside
    exact scratch_frame t flags a (by simpa only [active.out] using outside)
  have untagged : ∀ a : BitVec 64,
      (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      (errorTailReady (scratchReady t flags)).dmem.get? a = t.dmem.get? a := by
    intro a outside
    have outside' : ∀ i < 76, a ≠ t.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
      simpa only [active.out] using outside
    simp (disch := first | exact outside' | omega | decide) only
      [errorTailReady, errorTailMem, scratchReady, scratchMem,
        UInt64.toBitVec_ofNat, BoolCodec.store_frame (limit := 76)]
  apply return_tail_cps e base hc s (errorTailReady (scratchReady t flags)) limit data
    address capacity used ra h active.sp active.simd
  · change Large.Mapped (errorTailMem (scratchReady t flags)) t.regs.rdi.toBitVec 76
    unfold errorTailMem scratchReady scratchMem
    repeat' first | exact active.output | apply Large.mapped_store
  · exact savedAt_output s limit data address capacity used ra h ⟨nonempty, delimiter⟩
      t.dmem _ t.regs.rsp.toBitVec active.sp active.saved untagged
  · rw [model]
    simpa only [SszNative.Delimited.ResultAt, active.out] using
      scratch_result t flags (by simpa only [active.out] using h.output_bound)
  · simp only [model, SszNative.Delimited.Outcome.PreparedAt]
    intro ready impossible
    cases impossible
  · simpa only [model, SszNative.Delimited.Outcome.allocation, Option.bind_none] using
      frame_output s t.dmem _ data none h.output_bound frame written
  · rw [model]
    have bound := h.header_bound
    have separated := h.header_output
    rw [output_observe t.dmem _ s.regs.rdi.toBitVec h.output_bound written
      (s.regs.r8.toNat + 16) 8 (by omega)
      (by unfold Body.Apart at *; simp only [UInt64.toNat_toBitVec] at *; omega)]
    exact cursor
  · exact hp

/-- Rejection copies the original optional-capacity header and the actual
prepared pair, preserving any reservation made before comparison. -/
theorem over_limit_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (cap : Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s (some cap) data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (ready : SszNative.Delimited.Prepared)
    (state : Ready s t (some cap) data address capacity used ready)
    (rejected : ¬ ready.count.value ≤ cap) (capPointer capPayload : BitVec 64)
    (actualPointer : t.regs.rsi.toBitVec = BitVec.ofNat 64 ready.pointer)
    (spillPointer : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8 = some (capPointer.toNat : Int))
    (spillPayload : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (capPayload.toNat : Int))
    (originalPointer : widthLoad s.dmem (s.regs.rsi.toNat + 8) 8 = some capPointer.toNat)
    (originalPayload : widthLoad s.dmem (s.regs.rsi.toNat + 16) 8 = some capPayload.toNat)
    (P : MachineState → Prop)
    (hp : ∀ u, Post s (some cap) data address capacity used ra u → P u) :
    Eventually (step e) P (t, base + 454) := by
  have active : UsesActivation data := ⟨nonempty, delimiter⟩
  have apart : Large.Disjoint t.regs.rsp.toBitVec t.regs.rdi.toBitVec 40 76 := by
    have separated := activation_output_disjoint s (some cap) data address capacity used ra h active
    intro i hi j hj
    have location : t.regs.rsp.toBitVec + BitVec.ofNat 64 i =
        (s.regs.rsp.toBitVec - 104) + BitVec.ofNat 64 (16+i) := by
      rw [state.active.sp]
      bv_omega
    rw [location, state.active.out]
    exact separated (16+i) (by omega) j hj
  apply limit_stores_cps e base hc t capPointer capPayload state.active.output apart
    spillPointer spillPayload P
  apply error_tail_cps e base hc (limitReady t capPointer capPayload)
  · change Large.Mapped (limitMem t capPointer capPayload) t.regs.rdi.toBitVec 76
    unfold limitMem limitHeadMem
    repeat' first | exact state.active.output | apply Large.mapped_store
  · change 40 + 8 ≤ (76 : Nat)
    decide
  · change 48 + 8 ≤ (76 : Nat)
    decide
  let u := errorTailReady (limitReady t capPointer capPayload)
  have written : ∀ a : BitVec 64,
      (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      (tagged u).dmem.get? a = t.dmem.get? a := by
    intro a outside
    exact limit_frame t capPointer capPayload a (by simpa only [state.active.out] using outside)
  have untagged : ∀ a : BitVec 64,
      (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      u.dmem.get? a = t.dmem.get? a := by
    intro a outside
    have outside' : ∀ i < 76, a ≠ t.regs.rdi.toBitVec + BitVec.ofNat 64 i := by
      simpa only [state.active.out] using outside
    simp (disch := first | exact outside' | omega | decide) only
      [u, errorTailReady, errorTailMem, limitReady, limitMem, limitHeadMem,
        UInt64.toBitVec_ofNat, BoolCodec.store_frame (limit := 76)]
  have finalFrame : Frame s (tagged u).dmem data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩) := by
    simpa only [state.allocation] using frame_output s t.dmem (tagged u).dmem data
      ready.allocation h.output_bound state.frame written
  have pointerRead : widthLoad (tagged u).dmem (s.regs.rsi.toNat + 8) 8 = some capPointer.toNat := by
    rw [preserves_load s (some cap) data address capacity used ra h (tagged u).dmem finalFrame
      s.regs.rsi.toNat 24 8 8 h.option_owned (by decide)]
    exact originalPointer
  have payloadRead : widthLoad (tagged u).dmem (s.regs.rsi.toNat + 16) 8 = some capPayload.toNat := by
    rw [preserves_load s (some cap) data address capacity used ra h (tagged u).dmem finalFrame
      s.regs.rsi.toNat 24 16 8 h.option_owned (by decide)]
    exact originalPayload
  have expectedPair := SszNative.NatMemory.pair_of_at (widthLoad (tagged u).dmem)
    capPointer capPayload cap (s.regs.rsi.toNat + 8)
    (option_preserved s (some cap) data address capacity used ra h (tagged u).dmem finalFrame).2
    pointerRead (by simpa only [Nat.add_assoc, Nat.reduceAdd] using payloadRead)
  have actualPair := SszNative.Delimited.PreparedAt.pair (widthLoad (tagged u).dmem)
    ⟨address.toNat, capacity.toNat, used.toNat⟩ _ ready state.prepared
    (state.stored_output h (tagged u).dmem written) h.arena_bound h.arena_nonzero
  have bounds := ready_word_bounds h state
  apply ready_tail_cps e base hc s t u (some cap) data address capacity used ra h
    nonempty delimiter ready state rfl rfl
  · change Large.Mapped (errorTailMem (limitReady t capPointer capPayload)) t.regs.rdi.toBitVec 76
    unfold errorTailMem limitReady limitMem limitHeadMem
    repeat' first | exact state.active.output | apply Large.mapped_store
  · exact savedAt_output s (some cap) data address capacity used ra h active
      t.dmem _ t.regs.rsp.toBitVec state.active.sp state.active.saved untagged
  · exact written
  · rw [state.model nonempty delimiter]
    simp only [SszNative.Delimited.finish, rejected, ↓reduceIte, SszNative.Delimited.ResultAt]
    obtain ⟨tag, errorTag, index, ep, en, ap, an, zp, zn, reason⟩ :=
      limit_fields t capPointer capPayload (by simpa only [state.active.out] using h.output_bound)
    refine ⟨?_, ?_, ?_, ready, rfl, ?_, ?_⟩
    · simpa only [state.active.out] using limit_result t capPointer capPayload cap ready.count.value
        (by simpa only [state.active.out] using h.output_bound) expectedPair
        (by simpa only [actualPointer, state.payload] using actualPair)
    · simpa only [state.active.out, pointerRead] using ep
    · simpa only [state.active.out, payloadRead] using en
    · have pointerNat : t.regs.rsi.toNat = ready.pointer := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.1, UInt64.toNat_toBitVec] using
          congrArg BitVec.toNat actualPointer
      simpa only [state.active.out, pointerNat] using ap
    · have payloadNat : t.regs.r15.toNat = ready.payload := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.2, UInt64.toNat_toBitVec] using
          congrArg BitVec.toNat state.payload
      simpa only [state.active.out, payloadNat] using an
  · exact hp

end SszX86.Delimited
