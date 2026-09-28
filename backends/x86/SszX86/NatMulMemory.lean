import SszX86.NatMulResources

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem preserves_region (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (p n : Nat) (hp : Protected s address capacity used p n) :
    ∀ i < n, m.get? (BitVec.ofNat 64 (p+i)) = s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i inside
  have bound : p+i < 2^64 := by have := hp.bound; omega
  apply frame
  · apply ResultOutside.of_outside
    have apart := hp.output
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · have apart := hp.activation
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · intro r allocated
    have apartCursor := hp.cursor
    have apartArena := hp.arena
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    constructor <;> omega

theorem preserves_load (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (p n off count : Nat) (hp : Protected s address capacity used p n)
    (inside : off + count ≤ n) :
    widthLoad m (p + off) count = widthLoad s.dmem (p + off) count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [Nat.add_assoc] using
    preserves_region s left right address capacity used ra owned m frame p n hp
      (off+i) (by omega)

/-- Preserve the entire original operand, including redundant high zero limbs. -/
theorem operand_preserved (s : MachineData) (left right operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (stored : operand.At (widthLoad s.dmem))
    (hp : OperandProtected s address capacity used operand) :
    operand.At (widthLoad m) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [preserves_load s left right address capacity used ra owned m frame
      pointer.toNat (8 * words.length) (8 * i.val) 8 hp (by omega)]
    exact limbs i

theorem Frame.return_slot {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : Frame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have unchanged : Mem.loadInt m s.regs.rsp.toBitVec 8 = Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
    apply memmove_loadInt_congr
    intro i hi
    have bound := owned.return_bound
    have low := owned.stack_low
    have natural : (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rsp.toNat+i := by
      change s.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 at bound
      change (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rsp.toBitVec.toNat+i
      bv_omega
    apply frame
    · apply ResultOutside.of_outside
      rw [natural]
      have apart := owned.output_return
      unfold Body.Outside Body.Apart at *
      omega
    · rw [natural]
      unfold Body.Outside
      omega
    · intro r allocated
      rw [natural]
      have bounds := allocation_bounds s left right address capacity used ra owned r allocated
      have apartCursor := owned.cursor_return
      have apartArena := owned.arena_return
      have usedBound := owned.used_bound
      unfold Body.Outside Body.Apart at *
      constructor <;> omega
  exact unchanged.trans owned.return_load

/-- Result padding is protected against stack, cursor, and scratch writes too,
not merely against the final publication stores. -/
theorem Frame.output_byte {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : Frame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (i : Nat) (inside : i < 72)
    (untouched : ResultOutside
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result
      s.regs.rdi.toNat (s.regs.rdi.toNat+i)) :
    m.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) := by
  have bound := owned.output_bound
  have natural : (s.regs.rdi.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rdi.toNat+i := by
    change s.regs.rdi.toBitVec.toNat + 72 ≤ 2^64 at bound
    change (s.regs.rdi.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rdi.toBitVec.toNat+i
    bv_omega
  apply frame
  · simpa only [natural] using untouched
  · rw [natural]
    have apart := owned.output_stack
    unfold Body.Outside Body.Apart at *
    omega
  · intro r allocated
    rw [natural]
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apartCursor := owned.header_output
    have apartArena := owned.arena_output
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    constructor <;> omega

theorem Post.tail_padding {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (owned : Owned s left right address capacity used ra)
    (post : Post s left right address capacity used ra t) (i : Nat) (lo : 68 ≤ i) (hi : i < 72) :
    t.1.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) := by
  apply post.frame.output_byte owned i hi
  cases (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result <;>
    simp only [ResultOutside] <;> unfold Body.Outside <;> omega

theorem Post.success_padding {s : MachineData} {left right result : NatOperand}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (owned : Owned s left right address capacity used ra)
    (post : Post s left right address capacity used ra t)
    (success : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .ok result)
    (i : Nat) (lo : 16 ≤ i) (hi : i < 64) :
    t.1.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) := by
  apply post.frame.output_byte owned i (by omega)
  rw [success]
  unfold ResultOutside Body.Outside
  omega

/-- Composition only needs the execution-produced observations; preservation of
both original inputs follows from initial ownership and the precise frame. -/
theorem post_of_memory (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (t : MachineState)
    (observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result)
    (written : ∀ r,
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
      NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
        (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written)
    (returned : Returned s ra t)
    (frame : Frame s t.1.dmem (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (cursor : widthLoad t.1.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used) :
    Post s left right address capacity used ra t := by
  exact ⟨observed, written, returned, frame, cursor,
    operand_preserved s left right left address capacity used ra owned t.1.dmem frame
      owned.left_at owned.left_owned,
    operand_preserved s left right right address capacity used ra owned t.1.dmem frame
      owned.right_at owned.right_owned⟩

end SszX86.NatMul
