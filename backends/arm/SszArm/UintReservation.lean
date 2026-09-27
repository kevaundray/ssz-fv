import SszArm.UintArenaProofs

namespace SszArm.UintCodec

open SszNative

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Failed positive reservation reaches the real scratch-error tail without a
memory write; preserved registers include arguments, callee saves and SP. -/
theorem arena_failure (s : ArmState) (base : BitVec 64) (words : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 6776#64) (he : read_err s = .None)
    (hw : 0 < words) (hb : (r (.GPR 13) s).toNat = 8 * words) (hi : 8 * words < 2^63)
    (hn : Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat (arenaUsed s).toNat words = none) :
    let t := run (arenaTrace s).length s
    read_pc t = base + 4816#64 ∧ t.mem = s.mem ∧ CodeAt t base ∧
      read_err t = .None ∧ ∀ f, ArenaPreserved f → r f t = r f s := by
  have hchecks := (Arena.reserve_eq_none_iff_checks _ _ _ words hw).mp hn
  have hnot : (arenaTrace s).length ≠ 23 := by
    intro hf
    exact hchecks ((arena_passes_iff_checks s words hb hi).mp ((arena_trace_full s).mp hf))
  have hx := arena_trace_effect s base hp
  dsimp only at hx ⊢
  rw [arena_runs s base hc hp he]
  simp only [hnot, ↓reduceIte] at hx
  refine ⟨hx.1, hx.2.1, arenaBlock_code _ s base hc, ?_, ?_⟩
  · exact (arenaBlock_field _ s .ERR trivial).trans he
  · exact arenaBlock_field _ s

/-- Successful native reservation refines the exact pointer and cursor returned
by the checked-arithmetic model, and commits exactly that cursor word. The
positive-isize guard is the predecessor block's obligation. -/
theorem arena_success (s : ArmState) (base : BitVec 64) (words : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 6776#64) (he : read_err s = .None)
    (hw : 0 < words) (hb : (r (.GPR 13) s).toNat = 8 * words) (hi : 8 * words < 2^63)
    (reservation : Arena.Reservation)
    (hs : Arena.reserve (arenaBase s).toNat (arenaCapacity s).toNat (arenaUsed s).toNat words =
      some reservation) :
    let t := run (arenaTrace s).length s
    read_pc t = base + 6920#64 ∧
    (r (.GPR 12) t).toNat = reservation.pointer ∧
    (r (.GPR 16) t).toNat = reservation.used ∧
    t.mem = (write_mem_bytes 8 (r (.GPR 19) s + 16#64)
      (BitVec.ofNat 64 reservation.used) s).mem ∧
    r (.GPR 8) t = r (.GPR 8) s + 1#64 ∧
    r (.GPR 13) t = 0#64 ∧ r (.GPR 14) t = 0#64 ∧ r (.GPR 15) t = 8#64 ∧
    CodeAt t base ∧ read_err t = .None ∧
    ∀ f, ArenaPreserved f → r f t = r f s := by
  obtain ⟨hchecks, hr⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ words hw reservation).mp hs
  subst reservation
  have hpass := (arena_passes_iff_checks s words hb hi).mpr hchecks
  have hfull := (arena_trace_full s).mpr hpass
  have hpad := arena_padding_nat s hchecks.2.1 hchecks.2.2.1
  have hstart : (arenaStart s).toNat = Arena.start (arenaBase s).toNat (arenaUsed s).toNat := by
    rw [arenaStart, BitVec.toNat_add, Nat.mod_eq_of_lt hpass.2.2.1, hpad]
    simp only [Arena.start, Nat.add_comm]
  have hend : (arenaEnd s).toNat = Arena.finish (arenaBase s).toNat (arenaUsed s).toNat words := by
    rw [arenaEnd, BitVec.toNat_add, Nat.mod_eq_of_lt hpass.2.2.2.1, hstart, hb]
    rfl
  have hpointerBound : (arenaBase s).toNat + Arena.start (arenaBase s).toNat (arenaUsed s).toNat < 2^64 := by
    rw [Arena.start_pointer]
    have h := (Arena.aligned_bounds ((arenaBase s).toNat + (arenaUsed s).toNat)).2
    exact Nat.lt_of_le_of_lt h hchecks.2.2.1
  have hpointer : (arenaBase s + arenaStart s).toNat =
      (arenaBase s).toNat + Arena.start (arenaBase s).toNat (arenaUsed s).toNat := by
    rw [BitVec.toNat_add, hstart, Nat.mod_eq_of_lt hpointerBound]
  have hword : arenaEnd s = BitVec.ofNat 64 (Arena.finish (arenaBase s).toNat (arenaUsed s).toNat words) := by
    rw [← hend, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hx := arena_trace_effect s base hp
  dsimp only at hx ⊢
  rw [arena_runs s base hc hp he]
  simp only [hfull, ↓reduceIte] at hx
  have regs := hx.2.2 trivial
  refine ⟨hx.1, ?_, ?_, ?_, regs.2.2.1, regs.2.2.2.1, regs.2.2.2.2.1,
    regs.2.2.2.2.2, arenaBlock_code _ s base hc, ?_, arenaBlock_field _ s⟩
  · rw [regs.1, hpointer]
  · rw [regs.2.1, hend]
  · simpa only [hword] using hx.2.1
  · exact (arenaBlock_field _ s .ERR trivial).trans he

end SszArm.UintCodec
