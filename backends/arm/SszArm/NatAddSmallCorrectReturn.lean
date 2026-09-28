import SszArm.NatAddSmallCorrectMemory

namespace SszArm.NatAdd.SmallCorrect

open UintCodec SszNative
open Delimited (Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- A scratch-failure tail is composed against the original phase state, not a
new ownership predicate for clobbered X2/X4. -/
theorem error_finish (s u : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right) (prefixFrame : ZeroFrame s u)
    (hc : CodeAt u base) (he : read_err u = .None) (ha : CheckSPAlignment u)
    (hp : read_pc u = base + 1248#64)
    (model : outcome s left right = NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted)) :
    ∃ fuel t, run fuel u = t ∧ Post s t left right := by
  let t := errorResult .scratch base u
  have memory : MemoryFrame (localWrites s) s t := prefixFrame.memory.trans
    (by simpa only [prefixFrame.writes] using error_frame .scratch u base (prefixFrame.owned owned.return_owned))
  refine ⟨50, t, error_run .scratch u base hc he ha hp, ?_⟩
  apply post_of_frame s t left right owned (prefixFrame.returned (error_returned .scratch u base he))
  · have image := error_image .scratch u base (prefixFrame.owned owned.return_owned)
    simpa only [model, NatArithmetic.unchanged, prefixFrame.out] using image
  · intro reservation allocated
    simp only [model, NatArithmetic.unchanged] at allocated
    cases allocated
  · have bound := owned.arenaBound
    have address : (r (.GPR 5#5) s + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by bv_omega
    have cursor := memory.read (r (.GPR 5#5) s + 16#64) 8
      (by rw [address]; omega)
      (by rw [address]; exact owned.arenaLocal.subspan 16 8 (by decide))
    simpa only [model, NatArithmetic.unchanged, arenaOf] using congrArg BitVec.toNat cursor
  · simpa only [model, NatArithmetic.unchanged, writesFor] using memory

/-- The allocated return preserves all sixteen freshly written bytes. Its model
is the exact committed two-word result, including the original cursor update. -/
theorem allocated_finish (s u v : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right) (prefixFrame : ZeroFrame s u)
    (h5 : r (.GPR 5#5) u = r (.GPR 5#5) s)
    (h9 : r (.GPR 9#5) u = low left right)
    (hl : left.wordCount = 1) (hr : right.wordCount = 1)
    (overflow : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used 2 = some reservation)
    (frame : ArenaFrame u v) (success : ArenaSmallSuccess u v base reservation)
    (hc : CodeAt v base) (he : read_err v = .None) (ha : CheckSPAlignment v) :
    ∃ fuel t, run fuel v = t ∧ Post s t left right := by
  have geometry := reservation_geometry owned reservation reserved
  have pointerBound : reservation.pointer < 2^64 := by omega
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer := Nat.mod_eq_of_lt pointerBound
  have pointer : r (.GPR 8#5) v = BitVec.ofNat 64 reservation.pointer := by
    apply BitVec.eq_of_toNat_eq
    exact success.pointer.trans pointerNat.symm
  have fresh := reservation_fresh owned hl hr overflow reservation reserved
  have localFresh := fresh_local fresh
  have vout : r (.GPR 0#5) v = r (.GPR 0#5) s :=
    (frame.registers _ (by decide)).trans prefixFrame.out
  have vsp : r (.GPR 31#5) v = r (.GPR 31#5) s := frame.sp.trans prefixFrame.sp
  have locals : localWrites v = localWrites s := by simp only [localWrites, vout, vsp]
  have returnOwned : ReturnOwned v := by
    have original := owned.return_owned
    refine ⟨?_, ?_, ?_⟩
    · simpa only [vsp] using original.stack
    · simpa only [vout] using original.output
    · simpa only [vout, vsp] using original.separate
  let operand : NatOperand := .large (BitVec.ofNat 64 reservation.pointer) [low left right, 1#64]
  have input : operand.At (widthLoad v) := by
    simpa only [operand, h9] using allocated_at u v base reservation success
      geometry.1 geometry.2.1 geometry.2.2.1
  have borrowed : OperandOwned (localWrites v) operand := by
    simpa only [operand, OperandOwned, pointerNat, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, locals] using localFresh
  obtain ⟨fuel, t, executed, returned, returnMemory, image⟩ :=
    value_zero_run .wide v base hc he ha success.pc returnOwned operand
      (by simpa only [valuePointer, operand, NatOperand.pointer] using pointer)
      (by simp [valuePayload, operand, NatOperand.payload]) input borrowed
  have model : outcome s left right = NatArithmetic.committed reservation [low left right, 1#64] := by
    rw [model_overflow s left right hl hr overflow, reserved]
  have bound := owned.arenaBound
  have cursorAddress : (r (.GPR 5#5) s + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by bv_omega
  have allocationMemory : MemoryFrame (writesFor s (outcome s left right)) u v := by
    apply success.frame.weaken
    intro span member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [writesFor, model, NatArithmetic.committed, h5, cursorAddress]
  have terminalMemory : MemoryFrame (localWrites s) v t := by
    simpa only [locals] using returnMemory
  have terminalAllowed : MemoryFrame (writesFor s (outcome s left right)) v t := by
    apply terminalMemory.weaken
    intro span member
    simp only [writesFor, model, NatArithmetic.committed]
    exact List.mem_append_left _ member
  have memory : MemoryFrame (writesFor s (outcome s left right)) s t :=
    (local_frame _ prefixFrame.memory).trans (allocationMemory.trans terminalAllowed)
  refine ⟨fuel, t, executed, ?_⟩
  apply post_of_frame s t left right owned (prefixFrame.returned (arena_returned frame returned))
  · simpa only [model, NatArithmetic.committed, committed_pair, vout, operand] using image
  · intro actual allocated
    have same : actual = reservation := by
      simpa only [model, NatArithmetic.committed, Option.some.injEq] using allocated.symm
    subst actual
    have atFinal : operand.At (widthLoad t) := image.1.2.2
    have stored := atFinal.2.2.2
    simpa only [model, NatArithmetic.committed, operand, pointerNat] using stored
  · have preserveCursor := terminalMemory.read (r (.GPR 5#5) s + 16#64) 8
      (by rw [cursorAddress]; omega)
      (by rw [cursorAddress]; exact owned.arenaLocal.subspan 16 8 (by decide))
    have committedCursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) v =
        BitVec.ofNat 64 reservation.used := by simpa only [h5] using success.cursor
    rw [preserveCursor, committedCursor]
    simpa only [model, NatArithmetic.committed, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt geometry.2.2.2]
  · exact memory

end SszArm.NatAdd.SmallCorrect
