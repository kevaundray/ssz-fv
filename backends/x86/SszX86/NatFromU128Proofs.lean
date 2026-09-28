import SszX86.NatFromU128Resources

namespace SszX86.NatFromU128
open SszNative UintCodec

structure Preserved (s t : MachineData) : Prop where
  stack : t.regs.rsp = s.regs.rsp
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  vectors : t.zmms = s.zmms

theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (wide : BitVec 128) (address capacity used ra : BitVec 64)
    (owned : Owned s wide address capacity used ra)
    (memory : t.dmem = resultMem s address capacity used wide) (abi : Preserved s t) :
    Eventually (step e) (Post s wide address capacity used ra) (t, base + 19) ∧
    Eventually (step e) (Post s wide address capacity used ra) (t, base + 105) ∧
    Eventually (step e) (Post s wide address capacity used ra) (t, base + 176) := by
  have ret := result_return s wide address capacity used ra owned
  apply ret_cps e base hc t ra
  · simpa only [memory, abi.stack] using ret
  · apply post_of_memory s wide address capacity used ra owned _ memory
    exact ⟨rfl, by simp only [abi.stack], abi.rbx, abi.rbp, abi.r12, abi.r13,
      abi.r14, abi.r15, abi.vectors, by simpa only [memory] using ret⟩

private theorem reservation_abi (s t : MachineData) (flags : StatusFlags)
    (frame : Reservation.Frame (initial s flags) t) : Preserved s t := by
  have reg (r : Reg64) (h1 : r ≠ .r8) (h2 : r ≠ .r9) (h3 : r ≠ .r10) (h4 : r ≠ .r11) :=
    frame.registers r h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.vectors⟩
  all_goals apply UInt64.eq_of_toBitVec_eq
  · exact reg .rsp (by decide) (by decide) (by decide) (by decide)
  · exact reg .rbx (by decide) (by decide) (by decide) (by decide)
  · exact reg .rbp (by decide) (by decide) (by decide) (by decide)
  · exact reg .r12 (by decide) (by decide) (by decide) (by decide)
  · exact reg .r13 (by decide) (by decide) (by decide) (by decide)
  · exact reg .r14 (by decide) (by decide) (by decide) (by decide)
  · exact reg .r15 (by decide) (by decide) (by decide) (by decide)

/-- Complete actual47-instruction Nat::from_u128. The only premises describe
original caller-owned physical input, output, arena suffix and return storage.
All allocator guards, both payload stores, result publication and RET execute. -/
theorem from_u128_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (wide : BitVec 128) (address capacity used ra : BitVec 64)
    (owned : Owned s wide address capacity used ra) :
    Eventually (step e) (Post s wide address capacity used ra) (s, base + Int64.ofNat entry) := by
  rw [show Int64.ofNat entry = 0 by decide, Int64.add_zero]
  apply entry_cps e base hc s
  · intro high flags
    have small := (wide_small_iff wide).2 (owned.high.symm.trans high)
    apply small_cps e base hc (initial s flags) owned.output_mapped rfl
    intro flags'
    apply (finish_cps e base hc s _ wide address capacity used ra owned ?_ ?_).1
    · simp only [smallState, initial, resultMem, small, ↓reduceIte, owned.low]
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro high flags
    have large : ¬ wide.toNat < 2^64 := fun small => high (owned.high.trans ((wide_small_iff wide).1 small))
    apply eventually_trans (step e) (Reservation.Post (initial s flags) base address capacity used)
      (Post s wide address capacity used ra) _
      (Reservation.runs e base hc (initial s flags) address capacity used
        ⟨owned.header.address_load, owned.header.capacity_load, owned.header.used_load⟩)
    rintro ⟨t, pc⟩ ⟨frame, branch⟩
    rcases branch with ⟨failed, rfl⟩ | ⟨r, reserved, rfl, flags', rfl⟩
    · have out : t.regs.rdi = s.regs.rdi := UInt64.eq_of_toBitVec_eq
        (frame.registers .rdi (by decide) (by decide) (by decide) (by decide))
      have abi := reservation_abi s t flags frame
      have memory : t.dmem = s.dmem := frame.memory
      apply error_cps e base hc t
      · simpa only [OutputMapped, memory, out] using owned.output_mapped
      intro flags'
      apply (finish_cps e base hc s _ wide address capacity used ra owned ?_ ?_).2.2
      · simp only [errorState, resultMem, large, ↓reduceIte, failed, memory, out]
      · exact ⟨abi.stack, abi.rbx, abi.rbp, abi.r12, abi.r13, abi.r14, abi.r15, abi.vectors⟩
    · obtain ⟨checks, rfl⟩ :=
        (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
      have pointer : address + BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat) =
          BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat) := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      apply commit_cps e base hc
      · exact ⟨_, owned.header.used_load⟩
      · simpa only [Reservation.Ready, initial, UInt64.toBitVec_ofNat', pointer] using
          reserve_mapped s wide address capacity used ra owned _ reserved
      apply success_cps e base hc
      · dsimp only [OutputMapped, committed, commitMem, Reservation.Ready, initial]
        repeat' first | exact owned.output_mapped | apply Large.mapped_store
      · rfl
      apply (finish_cps e base hc s _ wide address capacity used ra owned ?_ ?_).2.1
      · simp only [resultMem, large, ↓reduceIte, reserved, committed, Reservation.Ready, initial,
          UInt64.toBitVec_ofNat', pointer, owned.low, owned.high, SszNative.Arena.finish]
        rfl
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem from_u128_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (wide : BitVec 128) (address capacity used ra : BitVec 64)
    (owned : Owned s wide address capacity used ra) :
    Eventually (step e)
      (fun t => NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
        (NatArithmetic.fromWide address.toNat capacity.toNat used.toNat wide).result)
      (s, base + Int64.ofNat entry) := by
  apply eventually_weaken (step e) (Post s wide address capacity used ra)
  · intro t post
    exact post.observed
  · exact from_u128_correct e base hc s wide address capacity used ra owned

theorem from_u128_value (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (wide : BitVec 128) (address capacity used ra : BitVec 64)
    (owned : Owned s wide address capacity used ra) :
    Eventually (step e) (fun t => Post s wide address capacity used ra t ∧
      ∀ operand, (outcome address capacity used wide).result = .ok operand →
        NatMemory.Pair (widthLoad t.1.dmem) operand.pointer operand.payload wide.toNat)
      (s, base + Int64.ofNat entry) := by
  apply eventually_weaken (step e) (Post s wide address capacity used ra)
  · intro t post
    refine ⟨post, ?_⟩
    intro operand success
    have observed := post.observed
    rw [success] at observed
    have pair := NatArithmetic.operandAt.pair _ _ operand observed.1
    rw [NatArithmetic.fromWide_value _ _ _ wide operand success] at pair
    exact pair
  · exact from_u128_correct e base hc s wide address capacity used ra owned

end SszX86.NatFromU128
