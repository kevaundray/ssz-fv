import SszX86.BitListListMemory

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

theorem list_protected (s : MachineData) (pointer payload ra : BitVec 64) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (low : 112 ≤ s.regs.rsp.toNat)
    (p n : Nat) (h : Protected s false address capacity used p n) :
    Delimited.Protected (listState s pointer payload ra) data address capacity used p n := by
  have sp := list_spNat s pointer payload ra low
  have active := activation_le data
  rcases h with ⟨hb, ho, hw, hc, ha⟩
  refine ⟨hb, ?_, ?_, hc, ha⟩
  · change Body.Apart p n s.regs.rdi.toNat 76
    unfold Body.Apart at *
    omega
  · rw [sp]
    simp only [workStart, workBytes, Bool.false_eq_true, ↓reduceIte] at hw
    unfold Body.Apart at *
    omega

theorem list_cap_owned (s : MachineData) (saved : Saved) (cap : Nat)
    (pointer payload ra : BitVec 64) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) :
    NatMemory.Pair (widthLoad (listState s pointer payload ra).dmem) pointer payload cap ∧
    (∀ p limbs, NatMemory.largeAt (widthLoad (listState s pointer payload ra).dmem)
      (s.regs.rsp.toNat + 24) p limbs →
      Protected s false address capacity used p (8 * limbs.length)) := by
  have hpRaw : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 =
      some (pointer.toNat : Int) := h.pointer_load
  have hnRaw : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
      some (payload.toNat : Int) := h.payload_load
  have hp : widthLoad s.dmem (s.regs.rbp.toNat + 8) 8 = some pointer.toNat := by
    simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address, hpRaw, Option.map_some, Int.toNat_natCast]
  have hn : widthLoad s.dmem (s.regs.rbp.toNat + 8 + 8) 8 = some payload.toNat := by
    simp only [widthLoad, Nat.add_assoc, Nat.reduceAdd, ← UInt64.toNat_toBitVec, width_address,
      hnRaw, Option.map_some, Int.toNat_natCast]
  have fields := list_fields s pointer payload ra
  rcases h.cap_pair with ⟨zero, value⟩ | ⟨capLimbs, positive, aligned, bound, count, limbsAt, value⟩
  · refine ⟨Or.inl ⟨zero, value⟩, ?_⟩
    intro p limbs large
    have same := Option.some.inj (large.2.2.2.2.1.symm.trans fields.2.2.1)
    simp only [zero, BitVec.toNat_zero] at same
    have := large.1
    omega
  · have original : NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8)
        pointer.toNat capLimbs :=
      ⟨positive, pointer.isLt, aligned, bound, hp, by simpa only [count] using hn, limbsAt⟩
    have protection := h.borrowed capLimbs original
    refine ⟨Or.inr ⟨capLimbs, positive, aligned, bound, count, ?_, value⟩, ?_⟩
    · intro i
      have sub := protection.subrange (8 * i.val) 8 (by have := i.isLt; omega)
      rw [list_width s pointer payload ra (h.stack_low rfl) h.stack_bound _ _ sub.bound sub.work]
      exact limbsAt i
    · intro p limbs large
      have sameP := Option.some.inj (large.2.2.2.2.1.symm.trans fields.2.2.1)
      have sameN := Option.some.inj (large.2.2.2.2.2.1.symm.trans
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using fields.2.2.2))
      have equal : limbs.length = capLimbs.length := sameN.trans count
      simpa only [sameP, equal] using protection

/-- Physical ownership for the real CALL is derived from the descriptor copy,
the CALL's actual return-slot store, and the caller's original reservations. -/
theorem list_owned (s : MachineData) (saved : Saved) (cap : Nat)
    (pointer payload ra : BitVec 64) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) :
    Delimited.Owned (listState s pointer payload ra) (some cap) data address capacity used ra := by
  have low := h.stack_low rfl
  have high := h.stack_bound
  have sp := list_spNat s pointer payload ra low
  have opt := list_optionNat s pointer payload ra high
  have active := activation_le data
  have fields := list_fields s pointer payload ra
  have capOwned := list_cap_owned s saved cap pointer payload ra data address capacity used h
  have outputWork := h.output_work
  have arenaWork := h.arena_work
  have headerWork := h.header_work
  simp only [workStart, workBytes, Bool.false_eq_true, ↓reduceIte] at outputWork arenaWork headerWork
  have headerLoad (j n : Nat) (within : j + n ≤ 24) :
      Mem.loadInt (listState s pointer payload ra).dmem
        (s.regs.rbx.toBitVec + BitVec.ofNat 64 j) n =
      Mem.loadInt s.dmem (s.regs.rbx.toBitVec + BitVec.ofNat 64 j) n := by
    have result := list_load s pointer payload ra low high (s.regs.rbx.toNat + j) n
      (by have := h.header_bound; omega)
      (by simp only [workStart, workBytes, Bool.false_eq_true, ↓reduceIte]; unfold Body.Apart at *; omega)
    simpa only [← UInt64.toNat_toBitVec, width_address] using result
  refine {
    output_bound := by change s.regs.rdi.toNat + 76 ≤ 2^64; have := h.output_bound; omega
    output_mapped := list_mapped s pointer payload ra _ _ (fun i hi => h.output_mapped i (by omega))
    return_bound := by rw [sp]; omega
    return_load := fields.1
    stack_low := by intro _; rw [sp]; omega
    stack_mapped := ?_
    output_return := ?_
    output_stack := ?_
    option_at := ?_
    option_owned := ?_
    borrowed := ?_
    length := h.length
    source := ?_
    source_owned := list_protected s pointer payload ra data address capacity used low _ _ h.source_owned
    header_bound := h.header_bound
    address_load := ?_
    capacity_load := ?_
    used_load := ?_
    arena_bound := h.arena_bound
    used_bound := h.used_bound
    arena_nonzero := h.arena_nonzero
    arena_mapped := list_mapped s pointer payload ra _ _ h.arena_mapped
    arena_output := ?_
    arena_stack := ?_
    arena_return := ?_
    arena_header := h.arena_header
    header_output := ?_
    header_stack := ?_
    cursor_return := ?_ }
  · intro _
    have equal : (listState s pointer payload ra).regs.rsp.toBitVec - 104 =
        BitVec.ofNat 64 (workStart s false) := by
      simp only [listState, UInt64.toBitVec_ofBitVec, workStart, Bool.false_eq_true, ↓reduceIte]
      simp only [← UInt64.toNat_toBitVec] at low ⊢
      bv_omega
    rw [equal]
    exact list_mapped s pointer payload ra _ _ (fun i hi => h.work_mapped i (by change i < 152; omega))
  · change Body.Apart s.regs.rdi.toNat 76 (listState s pointer payload ra).regs.rsp.toNat 8
    rw [sp]
    unfold Body.Apart at *
    omega
  · change Body.Apart s.regs.rdi.toNat 76
      ((listState s pointer payload ra).regs.rsp.toNat - 104) (Delimited.activationBytes data)
    rw [sp]
    unfold Body.Apart at *
    omega
  · rw [opt]
    refine ⟨fields.2.1, ?_⟩
    apply capOwned.1.at
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using fields.2.2.1
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using fields.2.2.2
  · rw [opt]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · change Body.Apart (s.regs.rsp.toNat + 16) 24 s.regs.rdi.toNat 76
      unfold Body.Apart at *
      omega
    · rw [sp]
      unfold Body.Apart
      omega
    · change Body.Apart (s.regs.rsp.toNat + 16) 24 (s.regs.rbx.toNat + 16) 8
      unfold Body.Apart at *
      omega
    · unfold Body.Apart at *
      omega
  · intro other equal p limbs large
    apply list_protected s pointer payload ra data address capacity used low
    apply capOwned.2 p limbs
    simpa only [opt, Nat.add_assoc, Nat.reduceAdd] using large
  · intro i hi
    have sub := h.source_owned.subrange i 1 (by omega)
    have kept := list_load s pointer payload ra low high _ _ sub.bound sub.work
    have kept' : Mem.loadInt (listState s pointer payload ra).dmem
        (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) 1 =
        Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) 1 := by
      simpa only [← UInt64.toNat_toBitVec, width_address] using kept
    exact kept'.trans (h.source i hi)
  · have kept := headerLoad 0 8 (by decide)
    simp only [BitVec.add_zero] at kept
    exact kept.trans h.address_load
  · exact (headerLoad 8 8 (by decide)).trans h.capacity_load
  · exact (headerLoad 16 8 (by decide)).trans h.used_load
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
      ((listState s pointer payload ra).regs.rsp.toNat - 104) (Delimited.activationBytes data)
    rw [sp]
    unfold Body.Apart at *
    omega
  · change Body.Apart (s.regs.rbx.toNat + 16) 8 (listState s pointer payload ra).regs.rsp.toNat 8
    rw [sp]
    unfold Body.Apart at *
    omega

end SszX86.BitList
