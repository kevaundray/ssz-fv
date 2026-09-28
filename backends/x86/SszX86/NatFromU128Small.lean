import SszX86.NatFromU128Memory

namespace SszX86.NatFromU128
open SszNative UintCodec
open NatToU128 (ByteFrame narrow_load_preserved)

/-- Small conversion never reads RCX or any arena storage. Only the actual
result stores and the original RET slot need physical ownership. -/
structure SmallOwned (s : MachineData) (low ra : BitVec 64) : Prop where
  low : s.regs.rsi.toBitVec = low
  high_zero : s.regs.rdx.toBitVec = 0
  output_mapped : OutputMapped s
  output_bound : s.regs.rdi.toNat + 68 ≤ 2^64
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  output_return : Body.Apart s.regs.rdi.toNat 68 s.regs.rsp.toNat 8

structure SmallPost (s : MachineData) (low ra : BitVec 64) (t : MachineState) : Prop where
  returned : Delimited.Returned s ra t
  observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat (.ok (.small low))
  memory : t.1.dmem = successMem s.dmem s.regs.rdi.toBitVec 0 low
  status : t.1.regs.rax = 0
  frame : ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 16 →
    Body.Outside a.toNat (s.regs.rdi.toNat+64) 4 → t.1.dmem.get? a = s.dmem.get? a

/-- Actual entry-to-RET Small path with no arena, capacity, alignment, allocator
or scratch premise. The only changed bytes are the pair and four-byte status. -/
theorem small_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (low ra : BitVec 64) (owned : SmallOwned s low ra) :
    Eventually (step e) (SmallPost s low ra) (s, base + Int64.ofNat entry) := by
  have frame : ByteFrame s.dmem (successMem s.dmem s.regs.rdi.toBitVec 0 low) s.regs.rdi.toNat 68 := by
    intro a outside
    exact NatAdd.success_mem_frame _ _ _ _ _
      (fun i hi => Body.outside_byte _ _ _ i owned.output_bound outside hi)
  have returnLoad : Mem.loadInt (successMem s.dmem s.regs.rdi.toBitVec 0 low) s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
    have same := narrow_load_preserved _ _ _ _ s.regs.rsp.toNat 8 frame owned.return_bound owned.output_return.symm
    simpa only [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq, owned.return_load] using same
  rw [show Int64.ofNat entry = 0 by decide, Int64.add_zero]
  apply entry_cps e base hc s
  · intro _ flags
    apply small_cps e base hc (initial s flags) owned.output_mapped rfl
    intro flags'
    apply (ret_cps e base hc (smallState (initial s flags) flags') ra (SmallPost s low ra) ?_ ?_).1
    · simpa only [smallState, initial, owned.low] using returnLoad
    · refine ⟨?_, ?_, ?_, rfl, ?_⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          by simpa only [smallState, initial, owned.low] using returnLoad⟩
      · have observed := NatAdd.success_reads s.dmem s.regs.rdi.toBitVec 0 low
        simpa [smallState, initial, owned.low, NatArithmetic.AddResultAt, NatArithmetic.operandAt,
          NatOperand.pointer, NatOperand.payload, NatOperand.At, successMem] using
          And.intro (And.intro observed.1 (And.intro observed.2.1 True.intro)) observed.2.2
      · simp only [smallState, initial, owned.low]
      · intro a pair status
        simp only [smallState, initial, owned.low]
        apply success_frame
        · intro i hi
          apply Body.outside_byte _ _ 16 i
          · rw [UInt64.toNat_toBitVec]
            have bound := owned.output_bound
            omega
          · exact pair
          · exact hi
        · intro i hi
          have bound := owned.output_bound
          simp only [← UInt64.toNat_toBitVec] at bound status
          unfold Body.Outside at status
          bv_omega
  · intro nonzero
    exact False.elim (nonzero owned.high_zero)

end SszX86.NatFromU128
