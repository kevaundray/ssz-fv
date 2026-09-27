import SszArm.NatDivisionSuccessPost
import SszArm.NatDivisionArenaInput
import SszArm.NatDivisionAllocated
import SszArm.NatDivisionPairWords

namespace SszArm.NatDivision

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Successful count-two reservation, both physical quotient stores, result
serialization, original activation restoration, and the actual RET. -/
theorem wide_reserved_post (original s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (remainder : BitVec 64)
    (reservation : SszNative.Arena.Reservation) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 684#64)
    (high : r (.GPR 1#5) s ≠ 0#64)
    (rem : r (.GPR 22#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s = remainder)
    (reserve : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used 2 = some reservation)
    (source : outcome original operand =
      { result := .ok (SszNative.NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
            [r (.GPR 0#5) s, r (.GPR 1#5) s], remainder)
        used := reservation.used, allocation := some reservation
        written := [r (.GPR 0#5) s, r (.GPR 1#5) s] })
    (before : MemoryFrame (localWrites original) original s) :
    ∃ fuel, Post original (run fuel s) operand := by
  let address := read_mem_bytes 8 (r (.GPR 4#5) original) original
  let capacity := read_mem_bytes 8 (r (.GPR 4#5) original + 8#64) original
  let used := read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) original
  have hbase : read_mem_bytes 8 (r (.GPR 21#5) s) s = address := by
    simpa [address] using local_arena_word owned before arena 0 (by decide)
  have hcapacity : read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s = capacity := by
    simpa [capacity] using local_arena_word owned before arena 8 (by decide)
  have hused : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = used := by
    simpa [used] using local_arena_word owned before arena 16 (by decide)
  have reserve' : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation := reserve
  have allocated : (outcome original operand).allocation = some reservation := by rw [source]
  have length : (outcome original operand).written.length = 2 := by rw [source]; rfl
  have geometry := owned.allocation_geometry reservation allocated
  have physical : (r (.GPR 21#5) s + 16#64).toNat + 8 ≤ 2^64 := by
    have h := owned.arenaBound
    rw [arena]
    bv_omega
  have fresh : ∀ target,
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some target →
      0 < target.pointer ∧ target.pointer % 8 = 0 ∧ target.pointer + 16 ≤ 2^64 ∧
      ((r (.GPR 21#5) s + 16#64).toNat + 8 ≤ target.pointer ∨
        target.pointer + 16 ≤ (r (.GPR 21#5) s + 16#64).toNat) := by
    intro target equal
    have same := Option.some.inj (equal.symm.trans reserve')
    subst target
    refine ⟨geometry.1, geometry.2.2.1, ?_, ?_⟩
    · simpa only [length] using geometry.2.2.2
    · rcases owned.fresh reservation allocated with empty | separate
      · rw [length] at empty
        omega
      · have apart := separate ((r (.GPR 4#5) original).toNat, 24) (by simp)
        simp only [Prod.fst, Prod.snd, length] at apart
        have h := owned.arenaBound
        rw [arena]
        bv_omega
  obtain ⟨fuel, t, executed, post⟩ := arena_small_reservation_runs s base address capacity used
    hc he ha hp hbase hcapacity hused
  have memory := arena_small_reservation_memory base address capacity used post physical fresh
  rw [reserve'] at memory
  rcases post with failed | ⟨native, u, checkpoint, pcu, pointeru, startu, finishu, result, _⟩
  · rw [reserve'] at failed
    cases failed.1
  · have expected := Option.some.inj (native.symm.trans reserve')
    have expectedPointer := congrArg SszNative.Arena.Reservation.pointer expected
    have committed : t = block base arenaSmallStoreOps u := result
    have frame : ArenaFrame s t := by
      rw [committed]
      exact checkpoint.frame.trans (arena_small_store_frame u base)
    have effect := arena_small_store_effect u base pcu
    rw [← committed] at effect
    have pointer : arenaSmallPointer u = BitVec.ofNat 64 reservation.pointer := by
      apply BitVec.eq_of_toNat_eq
      simp only [arenaSmallPointer, BitVec.toNat_add, pointeru, startu, BitVec.toNat_ofNat]
      rw [expectedPointer]
    have body := wide_commit_body_frame owned reservation allocated length arena memory.1
    have saved' := frame.saved_body owned body saved
    have out' := (frame.registers 19#5 (by decide)).trans out
    let quotient := SszNative.NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
      [r (.GPR 0#5) s, r (.GPR 1#5) s]
    have written : WrittenAt (widthLoad t) (outcome original operand) := by
      intro target equal
      have same := Option.some.inj (equal.symm.trans allocated)
      subst target
      have positive : 0 < (BitVec.ofNat 64 reservation.pointer).toNat := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt geometry.2.1] using geometry.1
      have words := pair_two_words (widthLoad t) (BitVec.ofNat 64 reservation.pointer)
        (r (.GPR 0#5) s) (r (.GPR 1#5) s) positive memory.2.2
      simpa only [source, BitVec.toNat_ofNat, Nat.mod_eq_of_lt geometry.2.1] using words
    have qAt : quotient.At (widthLoad t) := by
      simpa only [source] using allocated_operand_at owned reservation allocated written
    have qOwned : OperandOwned (returnWrites t) quotient := by
      simpa only [source] using allocated_operand_owned owned reservation allocated saved'.sp out'
    have qPointer : r (.GPR 9#5) t = quotient.pointer := by
      rw [effect.2.1, pointer]
      simp only [quotient, fromWords_two _ _ _ high, SszNative.NatOperand.pointer]
    have qPayload : r (.GPR 10#5) t = quotient.payload := by
      rw [effect.2.2.1]
      simp only [quotient, fromWords_two _ _ _ high, SszNative.NatOperand.payload, List.length_cons,
        List.length_nil]
    have remainder' : r (.GPR 22#5) t - r (.GPR 0#5) t * r (.GPR 20#5) t = remainder := by
      simpa only [frame.registers 22#5 (by decide), frame.registers 0#5 (by decide),
        frame.registers 20#5 (by decide)] using rem
    have cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) t).toNat =
        (outcome original operand).used := by
      simpa only [arena, source] using memory.2.1
    have final := wide_result_post original t base operand quotient remainder owned saved' out'
      (frame.code base hc) (frame.error.trans he) (frame.aligned ha) effect.1
      (by rw [source]) qPointer qPayload remainder' qAt qOwned written cursor
      ((local_frame (outcome original operand) before).trans (body_frame_full operand body))
    refine ⟨fuel + 24, ?_⟩
    rw [run_plus, executed]
    exact final

end SszArm.NatDivision
