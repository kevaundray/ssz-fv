import SszX86.MeasureBitsListCompare
import SszX86.MeasureBitsCommitStack
import SszX86.MeasureBitsFirstFailure
import SszX86.MeasureBitsControl

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

private theorem small_list_mem_as_spill (s : MachineData) :
    smallListMem s = spillMem s.dmem s.regs.rsp.toBitVec
      s.regs.rcx.toBitVec s.regs.r15.toBitVec := by
  with_unfolding_all rfl

theorem list_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (cap : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitList cap) (.bits bits) buffer address capacity used)
    (memory : t.dmem = s.dmem) (sp : t.regs.rsp = s.regs.rsp)
    (outReg : t.regs.rbx = s.regs.rbx) (headerReg : t.regs.rcx = s.regs.rcx)
    (vectors : t.zmms = s.zmms)
    (capPointer : t.regs.r13.toBitVec = cap.pointer)
    (capPayload : t.regs.r12.toBitVec = cap.payload)
    (low : t.regs.r15.toBitVec = bits.count.setWidth 64)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s (.bitList cap) (.bits bits) buffer address capacity used u.1)
      (t, base + 903) := by
  have work : Large.Mapped t.dmem t.regs.rsp.toBitVec 24 := by
    simpa only [memory, sp, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      body_work_mapped s _ _ buffer address capacity used owned 0 24 (by decide)
  have headerWords := arena_loads s.dmem s.regs.rcx.toBitVec address capacity used owned.arena
  apply list_high_cps e base hc
  intro flags
  by_cases small : bits.count.toNat < 2^64
  · have zero := (NatFromU128.wide_small_iff bits.count).1 small
    simp only [high, zero, ↓reduceIte]
    apply list_small_cps e base hc {t with status := flags} _ work
    intro zeroFlags
    let original := {t with status := flags}
    let prepared : MachineData :=
      {original with
        dmem := smallListMem original
        regs := {original.regs with rbp := 0}
        status := zeroFlags}
    have resources : CountPrefix s bits address capacity used prepared := by
      have initial := count_prefix_small s original (.bitList cap) bits buffer address capacity used
        owned small memory sp outReg vectors
      apply initial.stack_extension owned
      · simpa only [prepared, original, small_list_mem_as_spill, sp] using
          spill_frame s t.dmem t.regs.rcx.toBitVec t.regs.r15.toBitVec
      · exact spill_mapped _ _ _ _
      · rfl
      · rfl
      · rfl
    have native := NatFromU128.result_model_small address capacity used bits.count small
    change countCall bits address capacity used = _ at native
    have saved := spill_reads t.dmem t.regs.rsp.toBitVec t.regs.rcx.toBitVec t.regs.r15.toBitVec
    apply list_bound_cps e base hc helpers s prepared cap (.small (bits.count.setWidth 64)) bits
      buffer address capacity used owned resources
    · simp only [native, NatArithmetic.unchanged]
    · rfl
    · exact low
    · exact capPointer
    · exact capPayload
    · exact high
    · simpa only [prepared, original, small_list_mem_as_spill, low] using saved.2
    · simpa only [prepared, original, small_list_mem_as_spill, headerReg] using saved.1
  · have nonzero : (bits.count >>> 64).setWidth 64 ≠ 0#64 := by
      intro zero
      exact small ((NatFromU128.wide_small_iff bits.count).2 zero)
    simp only [high, nonzero, ↓reduceIte]
    apply eventually_trans (step e)
      (ListReservation.Post {t with status := flags} base address capacity used) _ _
      (ListReservation.runs e base hc _ address capacity used
        ⟨by simpa only [memory, headerReg] using headerWords.1,
          by simpa only [memory, headerReg] using headerWords.2.1,
          by simpa only [memory, headerReg] using headerWords.2.2⟩)
    rintro ⟨u, pc⟩ ⟨reservationFrame, branch⟩
    rcases branch with ⟨failed, rfl⟩ | ⟨r, reserved, rfl, readyFlags, rfl⟩
    · apply first_failure_cps e base hc s u (.bitList cap) (some cap) bits buffer address capacity used owned
        rfl small failed (reservationFrame.memory.trans memory)
      · exact (UInt64.eq_of_toBitVec_eq
          (reservationFrame.registers .rsp (by decide) (by decide) (by decide) (by decide))).trans sp
      · exact (UInt64.eq_of_toBitVec_eq
          (reservationFrame.registers .rbx (by decide) (by decide) (by decide) (by decide))).trans outReg
      · exact reservationFrame.vectors.trans vectors
    · obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
      have pointerWord : address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) =
          BitVec.ofNat 64 r.pointer := by
        rw [shape]
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have cursorWord : BitVec.ofNat 64 (Arena.start address.toNat used.toNat + 16) =
          BitVec.ofNat 64 r.used := by rw [shape]; rfl
      let ready := ListReservation.Ready {t with status := flags} address used readyFlags
      let committed := ListReservation.committed ready
      have memoryForm : committed.dmem = vectorCommitMem {s with dmem := smallListMem ready} r bits.count := by
        rw [show committed.dmem = ListReservation.commitMem ready by rfl,
          list_commit_form ready (by
            simpa only [ready, ListReservation.Ready, headerReg, sp] using
              cursor_spill_disjoint s _ _ buffer address capacity used owned)]
        simp only [vectorCommitMem, ready, ListReservation.Ready, headerReg, low, high,
          UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', pointerWord, cursorWord]
      have resources : CountPrefix s bits address capacity used committed := by
        apply count_prefix_committed s committed (.bitList cap) bits buffer address capacity used
          owned small r reserved (smallListMem ready)
        · simpa only [small_list_mem_as_spill, ready, ListReservation.Ready, memory, sp] using
            spill_frame s s.dmem t.regs.rcx.toBitVec t.regs.r15.toBitVec
        · simpa only [small_list_mem_as_spill, ready, ListReservation.Ready, memory] using
            spill_mapped s.dmem t.regs.rsp.toBitVec t.regs.rcx.toBitVec t.regs.r15.toBitVec
        · exact memoryForm
        · exact sp
        · exact outReg
        · exact vectors
      have saved := spill_reads ready.dmem ready.regs.rsp.toBitVec ready.regs.rcx.toBitVec ready.regs.r15.toBitVec
      have native := NatFromU128.result_model_success address capacity used bits.count small r reserved
      change countCall bits address capacity used = _ at native
      apply ListReservation.commit_cps e base hc
      · simpa only [ListReservation.Ready, memory, headerReg] using arena_mapped s.dmem s.regs.rcx.toBitVec
          address capacity used owned.arena
      · exact work
      · simpa only [ListReservation.Ready, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat',
          pointerWord, memory] using reserve_mapped s _ _ buffer address capacity used owned r reserved
      apply list_bound_cps e base hc helpers s committed cap
        (.large (BitVec.ofNat 64 r.pointer) [bits.count.setWidth 64, (bits.count >>> 64).setWidth 64]) bits
        buffer address capacity used owned resources
      · rw [native]
      · simpa only [committed, ListReservation.committed, ready, ListReservation.Ready,
          UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', NatOperand.pointer] using pointerWord
      · rfl
      · exact capPointer
      · exact capPayload
      · exact high
      · rw [memoryForm]
        have stackRead := commit_stack_load s _ _ buffer address capacity used owned
          (smallListMem ready) r bits.count reserved 16 8 (by decide)
        rw [small_list_mem_as_spill] at stackRead ⊢
        rw [show committed.regs.rsp = s.regs.rsp from sp]
        change Mem.loadInt _ (s.regs.rsp.toBitVec + 16#64) 8 = _
        rw [stackRead]
        have savedLow := saved.2
        simp only [ready, ListReservation.Ready, sp, low] at savedLow ⊢
        with_unfolding_all exact savedLow
      · rw [memoryForm]
        have stackRead := commit_stack_load s _ _ buffer address capacity used owned
          (smallListMem ready) r bits.count reserved 8 8 (by decide)
        rw [small_list_mem_as_spill] at stackRead ⊢
        rw [show committed.regs.rsp = s.regs.rsp from sp]
        change Mem.loadInt _ (s.regs.rsp.toBitVec + 8#64) 8 = _
        rw [stackRead]
        have savedHeader := saved.1
        simp only [ready, ListReservation.Ready, sp, headerReg] at savedHeader ⊢
        with_unfolding_all exact savedHeader

end SszX86.Measure.Bits
