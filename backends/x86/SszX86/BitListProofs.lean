import SszX86.BitListListOwned
import SszX86.BitListProgressiveProofs
import SszX86.BitListFrame

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

theorem list_combined_frame (s : MachineData) (saved : Saved) (cap : Nat)
    (pointer payload ra : BitVec 64) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) (t : MachineState)
    (post : Delimited.Post (listState s pointer payload ra) (some cap) data address capacity used ra t) :
    Frame s false t.1.dmem
      (SszNative.Delimited.run (some cap) data ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation := by
  have low := h.stack_low rfl
  have sp := list_spNat s pointer payload ra low
  intro a out work arena
  have helper : t.1.dmem.get? a = (listState s pointer payload ra).dmem.get? a := by
    apply post.frame a out
    · rw [sp]
      have active := activation_le data
      simp only [workStart, workBytes, Bool.false_eq_true, ↓reduceIte] at work
      unfold Body.Outside at *
      omega
    · exact arena
  exact helper.trans (list_frame s pointer payload ra low h.stack_bound a work)

theorem result_option_congr (observe : Nat → Nat → Option Nat) (out source left right : Nat)
    (data : Ssz.Bytes) (result : SszNative.Delimited.Outcome)
    (hp : observe (left + 8) 8 = observe (right + 8) 8)
    (hn : observe (left + 16) 8 = observe (right + 16) 8)
    (h : SszNative.Delimited.ResultAt observe out source left data result) :
    SszNative.Delimited.ResultAt observe out source right data result := by
  cases selected : result.result with
  | ok view => simpa only [SszNative.Delimited.ResultAt, selected] using h
  | error error =>
    cases error with
    | scratchExhausted => simpa only [SszNative.Delimited.ResultAt, selected] using h
    | semantic reason =>
      cases reason <;> simpa only [SszNative.Delimited.ResultAt, selected, hp, hn] using h

theorem list_observed (s : MachineData) (saved : Saved) (cap : Nat)
    (pointer payload ra : BitVec 64) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) (t : MachineState)
    (post : Delimited.Post (listState s pointer payload ra) (some cap) data address capacity used ra t) :
    SszNative.Delimited.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat s.regs.rdx.toNat
      s.regs.rbp.toNat data
      (SszNative.Delimited.run (some cap) data ⟨address.toNat, capacity.toNat, used.toNat⟩) := by
  have owned := list_owned s saved cap pointer payload ra data address capacity used h
  have frame := list_combined_frame s saved cap pointer payload ra data address capacity used h t post
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.r14.toBitVec.isLt
  have resources := (SszNative.Delimited.run_resources (some cap) data
    ⟨address.toNat, capacity.toNat, used.toNat⟩ physical).1
  have helperFrame : Delimited.Frame (listState s pointer payload ra) t.1.dmem data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩) := by
    simpa only [resources] using post.frame
  have opt := list_optionNat s pointer payload ra h.stack_bound
  have fields := list_fields s pointer payload ra
  have copyPointer := Delimited.preserves_load (listState s pointer payload ra) (some cap) data
    address capacity used ra owned t.1.dmem helperFrame
    (listState s pointer payload ra).regs.rsi.toNat 24 8 8 owned.option_owned (by decide)
  have copyPayload := Delimited.preserves_load (listState s pointer payload ra) (some cap) data
    address capacity used ra owned t.1.dmem helperFrame
    (listState s pointer payload ra).regs.rsi.toNat 24 16 8 owned.option_owned (by decide)
  have oldPointer := frame_preserves_load s saved false (some cap) data address capacity used
    h.toOwned t.1.dmem frame s.regs.rbp.toNat 24 8 8 h.descriptor (by decide)
  have oldPayload := frame_preserves_load s saved false (some cap) data address capacity used
    h.toOwned t.1.dmem frame s.regs.rbp.toNat 24 16 8 h.descriptor (by decide)
  have pointerRaw : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 =
      some (pointer.toNat : Int) := h.pointer_load
  have payloadRaw : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
      some (payload.toNat : Int) := h.payload_load
  have pointerRead : widthLoad t.1.dmem (s.regs.rbp.toNat + 8) 8 = some pointer.toNat := by
    unfold widthLoad
    rw [oldPointer]
    simp only [← UInt64.toNat_toBitVec, width_address, pointerRaw, Option.map_some, Int.toNat_natCast]
  have payloadRead : widthLoad t.1.dmem (s.regs.rbp.toNat + 16) 8 = some payload.toNat := by
    unfold widthLoad
    rw [oldPayload]
    simp only [← UInt64.toNat_toBitVec, width_address, payloadRaw, Option.map_some, Int.toNat_natCast]
  apply result_option_congr _ _ _ (listState s pointer payload ra).regs.rsi.toNat
    s.regs.rbp.toNat data _ _ _ post.observed
  · rw [copyPointer, opt]
    simpa only [Nat.add_assoc, Nat.reduceAdd, pointerRead] using fields.2.2.1
  · rw [copyPayload, opt]
    simpa only [Nat.add_assoc, Nat.reduceAdd, payloadRead] using fields.2.2.2

theorem list_saved (s : MachineData) (saved : Saved) (cap : Nat)
    (pointer payload ra : BitVec 64) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) (t : MachineState)
    (post : Delimited.Post (listState s pointer payload ra) (some cap) data address capacity used ra t) :
    SavedAt t.1.dmem s.regs.rsp.toBitVec saved := by
  have frame := list_combined_frame s saved cap pointer payload ra data address capacity used h t post
  have savedOwned : Protected s false address capacity used (s.regs.rsp.toNat + 312) 56 := by
    refine ⟨h.stack_bound, h.output_saved.symm, ?_, h.cursor_saved.symm, h.arena_saved.symm⟩
    have low := h.stack_low rfl
    simp only [workStart, workBytes, Bool.false_eq_true, ↓reduceIte]
    unfold Body.Apart
    omega
  have kept (j : Nat) (within : j + 8 ≤ 56) :
      Mem.loadInt t.1.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 (312 + j)) 8 =
        Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 (312 + j)) 8 := by
    have result := frame_preserves_load s saved false (some cap)
      data address capacity used h.toOwned t.1.dmem frame _ _ j 8 savedOwned within
    simpa only [Nat.add_assoc, ← UInt64.toNat_toBitVec, width_address] using result
  rcases h.saved with ⟨hb, h12, h13, h14, h15, hbp, hrip⟩
  exact ⟨(kept 0 (by decide)).trans hb, (kept 8 (by decide)).trans h12,
    (kept 16 (by decide)).trans h13, (kept 24 (by decide)).trans h14,
    (kept 32 (by decide)).trans h15, (kept 40 (by decide)).trans hbp,
    (kept 48 (by decide)).trans hrip⟩

/-- Actual BitList entry1192, the Some copy and real CALL, complete helper,
and the common six-register epilogue through the caller RET. -/
theorem list_correct (e : Executable) (base : Int64) (code : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (cap : Nat) (pointer payload : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) :
    Eventually (step e) (Post s saved false (some cap) data address capacity used)
      (s, base + Int64.ofNat listEntry) := by
  have low := h.stack_low rfl
  have callMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 48 := by
    have region := Delimited.Reservation.mapped_subrange s.dmem
      (BitVec.ofNat 64 (workStart s false)) 152 104 48 h.work_mapped (by decide)
    have slot : BitVec.ofNat 64 (workStart s false) + 104#64 = s.regs.rsp.toBitVec - 8 := by
      simp only [workStart, Bool.false_eq_true, ↓reduceIte, ← UInt64.toNat_toBitVec] at low ⊢
      bv_omega
    simpa only [slot] using region
  apply list_entry_cps e base code.body s pointer payload h.pointer_load h.payload_load callMapped
  have runs := Delimited.decode_correct e (base + Int64.ofInt delimitedOffset)
    code.delimited code.compare (listState s pointer payload (base + 1235).toBitVec)
    (some cap) data address capacity used (base + 1235).toBitVec
    (list_owned s saved cap pointer payload _ data address capacity used h)
  rw [show Int64.ofNat Delimited.entry = 0 by decide, Int64.add_zero] at runs
  apply eventually_trans (step e)
    (Delimited.Post (listState s pointer payload (base + 1235).toBitVec) (some cap) data
      address capacity used (base + 1235).toBitVec)
    (Post s saved false (some cap) data address capacity used)
    (listState s pointer payload (base + 1235).toBitVec, base + Int64.ofInt delimitedOffset)
    runs
  intro t post
  have sp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec := by
    have hs := post.returned.sp
    change t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8 + 8 at hs
    simpa only [BitVec.sub_add_cancel] using hs
  have pc : t.2 = base + 1235 := by
    simpa only [Int64.ofBitVec_toBitVec] using post.returned.pc
  have savedAt := list_saved s saved cap pointer payload _ data address capacity used h t post
  have observed := list_observed s saved cap pointer payload _ data address capacity used h t post
  have frame := list_combined_frame s saved cap pointer payload _ data address capacity used h t post
  rcases t with ⟨u, pc'⟩
  change u.regs.rsp.toBitVec = s.regs.rsp.toBitVec at sp
  change pc' = base + 1235 at pc
  subst pc'
  bitlist_step 9 using code.body
  apply epilogue_cps e base code.body u saved (by rw [sp]; exact savedAt)
  refine ⟨observed, post.prepared, ?_, frame, post.cursor⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, post.returned.simd, savedAt.2.2.2.2.2.2⟩
  · change u.regs.rsp.toBitVec + 368#64 = s.regs.rsp.toBitVec + 368#64
    rw [sp]
  all_goals rfl

end SszX86.BitList
