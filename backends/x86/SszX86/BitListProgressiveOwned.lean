import SszX86.BitListMemory

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

theorem Protected.subrange {s : MachineData} {tail : Bool}
    {address capacity used : BitVec 64} {p n : Nat}
    (h : Protected s tail address capacity used p n) (j k : Nat) (within : j + k ≤ n) :
    Protected s tail address capacity used (p + j) k := by
  rcases h with ⟨bound, output, work, cursor, arena⟩
  constructor
  · omega
  all_goals unfold Body.Apart at *; omega

theorem activation_le (data : Ssz.Bytes) : Delimited.activationBytes data ≤ 104 := by
  unfold Delimited.activationBytes
  split <;> omega

theorem progressive_spNat (s : MachineData) (saved : Saved)
    (bound : s.regs.rsp.toNat + 368 ≤ 2^64) :
    (progressiveState s saved).regs.rsp.toNat = s.regs.rsp.toNat + 360 := by
  simp only [progressiveState, UInt64.toNat_ofBitVec]
  simp only [← UInt64.toNat_toBitVec] at bound ⊢
  bv_omega

theorem progressive_optionNat (s : MachineData) (saved : Saved)
    (bound : s.regs.rbp.toNat + 32 ≤ 2^64) :
    (progressiveState s saved).regs.rsi.toNat = s.regs.rbp.toNat + 8 := by
  simp only [progressiveState, UInt64.toNat_ofBitVec]
  simp only [← UInt64.toNat_toBitVec] at bound ⊢
  bv_omega

theorem progressive_protected (s : MachineData) (saved : Saved) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (bound : s.regs.rsp.toNat + 368 ≤ 2^64)
    (p n : Nat) (h : Protected s true address capacity used p n) :
    Delimited.Protected (progressiveState s saved) data address capacity used p n := by
  have sp := progressive_spNat s saved bound
  have active := activation_le data
  rcases h with ⟨hb, ho, hw, hc, ha⟩
  refine ⟨hb, ?_, ?_, hc, ha⟩
  · change Body.Apart p n s.regs.rdi.toNat 76
    unfold Body.Apart at *
    omega
  · rw [sp]
    simp only [workStart, workBytes, ↓reduceIte] at hw
    unfold Body.Apart at *
    omega

/-- Ownership of the genuine tail-call entry follows from the original frame;
no caller return address is pushed and no helper outcome is assumed. -/
theorem progressive_owned (s : MachineData) (saved : Saved) (limit : Option Nat)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ProgressiveOwned s saved limit data address capacity used) :
    Delimited.Owned (progressiveState s saved) limit data address capacity used saved.rip := by
  have sp := progressive_spNat s saved h.stack_bound
  have opt := progressive_optionNat s saved h.descriptor.bound
  have active := activation_le data
  have outputWork := h.output_work
  have outputSaved := h.output_saved
  have arenaWork := h.arena_work
  have arenaSaved := h.arena_saved
  have headerWork := h.header_work
  have cursorSaved := h.cursor_saved
  simp only [workStart, workBytes, ↓reduceIte] at outputWork arenaWork headerWork
  refine {
    output_bound := by change s.regs.rdi.toNat + 76 ≤ 2^64; have := h.output_bound; omega
    output_mapped := fun i hi => h.output_mapped i (by omega)
    return_bound := by rw [sp]; have := h.stack_bound; omega
    return_load := h.saved.2.2.2.2.2.2
    stack_low := by intro _; rw [sp]; omega
    stack_mapped := ?_
    output_return := ?_
    output_stack := ?_
    option_at := by rw [opt]; exact h.option_at
    option_owned := ?_
    borrowed := ?_
    length := h.length
    source := h.source
    source_owned := progressive_protected s saved data address capacity used h.stack_bound _ _ h.source_owned
    header_bound := h.header_bound
    address_load := h.address_load
    capacity_load := h.capacity_load
    used_load := h.used_load
    arena_bound := h.arena_bound
    used_bound := h.used_bound
    arena_nonzero := h.arena_nonzero
    arena_mapped := h.arena_mapped
    arena_output := ?_
    arena_stack := ?_
    arena_return := ?_
    arena_header := h.arena_header
    header_output := ?_
    header_stack := ?_
    cursor_return := ?_ }
  · intro _
    have equal : (progressiveState s saved).regs.rsp.toBitVec - 104 =
        BitVec.ofNat 64 (workStart s true) := by
      simp only [progressiveState, UInt64.toBitVec_ofBitVec, workStart, ↓reduceIte,
        BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← UInt64.toNat_toBitVec]
      bv_omega
    rw [equal]
    exact h.work_mapped
  · change Body.Apart s.regs.rdi.toNat 76 (progressiveState s saved).regs.rsp.toNat 8
    rw [sp]
    unfold Body.Apart at *
    omega
  · change Body.Apart s.regs.rdi.toNat 76
      ((progressiveState s saved).regs.rsp.toNat - 104) (Delimited.activationBytes data)
    rw [sp]
    unfold Body.Apart at *
    omega
  · rw [opt]
    exact progressive_protected s saved data address capacity used h.stack_bound _ _
      (h.descriptor.subrange 8 24 (by decide))
  · intro cap hc p limbs hl
    apply progressive_protected s saved data address capacity used h.stack_bound
    apply h.borrowed cap hc p limbs
    rw [opt] at hl
    simpa only [progressiveState, Nat.add_assoc, Nat.reduceAdd] using hl
  · have := h.arena_output
    change Body.Apart _ _ s.regs.rdi.toNat 76
    unfold Body.Apart at *
    omega
  · rw [sp]
    unfold Body.Apart at *
    omega
  · rw [sp]
    unfold Body.Apart at *
    omega
  · have := h.header_output
    change Body.Apart s.regs.rbx.toNat 24 s.regs.rdi.toNat 76
    unfold Body.Apart at *
    omega
  · change Body.Apart s.regs.rbx.toNat 24
      ((progressiveState s saved).regs.rsp.toNat - 104) (Delimited.activationBytes data)
    rw [sp]
    unfold Body.Apart at *
    omega
  · change Body.Apart (s.regs.rbx.toNat + 16) 8 (progressiveState s saved).regs.rsp.toNat 8
    rw [sp]
    unfold Body.Apart at *
    omega

end SszX86.BitList
