import SszArm.NatAddArena

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Physical ownership needed only for a successful two-word reservation. -/
def ArenaSmallReservationOwned (s : ArmState) (reservation : SszNative.Arena.Reservation) : Prop :=
  (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64 ∧
  0 < reservation.pointer ∧ reservation.pointer + 16 ≤ 2^64 ∧
  ((r (.GPR 5#5) s + 16#64).toNat + 8 ≤ reservation.pointer ∨
    reservation.pointer + 16 ≤ (r (.GPR 5#5) s + 16#64).toNat)

def arenaSmallReservedMemory (s : ArmState) (reservation : SszNative.Arena.Reservation) : ArmState :=
  write_mem_bytes 16 (BitVec.ofNat 64 reservation.pointer)
    (1#64 ++ r (.GPR 9#5) s) (arenaCursorMemory s reservation)

structure ArenaSmallSuccess (s t : ArmState) (base : BitVec 64)
    (reservation : SszNative.Arena.Reservation) : Prop where
  pc : read_pc t = base + 1196#64
  pointer : (r (.GPR 8#5) t).toNat = reservation.pointer
  low : r (.GPR 9#5) t = r (.GPR 9#5) s
  high : r (.GPR 10#5) t = 1#64
  cursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = BitVec.ofNat 64 reservation.used
  memory : t.mem = (arenaSmallReservedMemory s reservation).mem
  frame : Delimited.MemoryFrame
    [((r (.GPR 5#5) s + 16#64).toNat, 8), (reservation.pointer, 16)] s t
  pair : SszNative.NatMemory.Pair (widthLoad t) (r (.GPR 8#5) t) 2#64
    ((r (.GPR 9#5) s).toNat + 2^64)

def ArenaSmallPost (s t : ArmState) (base address capacity used : BitVec 64) : Prop :=
  ArenaFrame s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none ∧
        read_pc t = base + 1248#64 ∧ t.mem = s.mem) ∨
      ∃ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation ∧
        ArenaSmallSuccess s t base reservation)

private theorem small_reservation_commit (s u : ArmState)
    (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (reached : ArenaCheckpoint s u) (hp : read_pc u = base + 1180#64)
    (h8 : r (.GPR 8#5) u = address)
    (h10 : (r (.GPR 10#5) u).toNat = SszNative.Arena.start address.toNat used.toNat)
    (h11 : (r (.GPR 11#5) u).toNat = SszNative.Arena.finish address.toNat used.toNat 2)
    (low : r (.GPR 9#5) u = r (.GPR 9#5) s)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2)
    (owned : ∀ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation →
      ArenaSmallReservationOwned s reservation) :
    ∃ fuel t, run fuel s = t ∧ ArenaSmallPost s t base address capacity used := by
  let reservation : SszNative.Arena.Reservation :=
    ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
      SszNative.Arena.finish address.toNat used.toNat 2⟩
  have success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation :=
    (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) reservation).2 ⟨checks, rfl⟩
  have ho := owned reservation success
  have pointerBound : reservation.pointer < 2^64 := by
    have bounds := SszNative.Arena.aligned_bounds (address.toNat + used.toNat)
    have eq := SszNative.Arena.start_pointer address.toNat used.toNat
    have round := checks.2.2.1
    dsimp [reservation]
    omega
  have pointer : (arenaSmallPointer u).toNat = reservation.pointer := by
    unfold arenaSmallPointer
    rw [h8, BitVec.toNat_add, h10, Nat.mod_eq_of_lt pointerBound]
  have pointerWord : arenaSmallPointer u = BitVec.ofNat 64 reservation.pointer := by
    rw [← pointer, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have finishWord : r (.GPR 11#5) u = BitVec.ofNat 64 reservation.used := by
    dsimp only [reservation]
    rw [← h11, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have r5 := reached.frame.registers 5#5 (by decide)
  have aligned : reservation.pointer % 8 = 0 := by
    dsimp [reservation]
    rw [SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  have commitOwned : ArenaSmallOwned u := by
    unfold ArenaSmallOwned
    rw [pointer, r5]
    exact ⟨ho.1, ho.2.1, aligned, ho.2.2.1, ho.2.2.2⟩
  let t := block base arenaSmallStoreOps u
  have effect := arena_small_store_effect u base hp
  have memory := arena_small_store_memory u base commitOwned hp
  have exactMemory : (arenaSmallMemory u).mem = (arenaSmallReservedMemory s reservation).mem := by
    unfold arenaSmallMemory arenaBigMemory arenaSmallReservedMemory arenaCursorMemory
    rw [pointerWord, finishWord, r5, low]
    apply mem_write_mem_bytes_of_mem_eq
    exact mem_write_mem_bytes_of_mem_eq reached.memory _ _ _
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := arena_small_store_run u base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨fuel + 4, t, ?_, reached.frame.trans (arena_small_store_frame u base),
    Or.inr ⟨reservation, success, ?_⟩⟩
  · rw [run_plus, hr, hrun]
  · refine ⟨effect.1, ?_, effect.2.2.1.trans low, effect.2.2.2.1, ?_,
      effect.2.2.2.2.trans exactMemory, ?_, ?_⟩
    · rw [effect.2.1]
      exact pointer
    · rw [← r5]
      exact memory.2.1.trans finishWord
    · intro a outside
      rw [← reached.memory]
      exact memory.1 a (by simpa only [pointer, r5] using outside)
    · rw [effect.2.1, ← low]
      exact memory.2.2

/-- Complete two-word reservation, including each failure branch, the real
cursor store, and the paired low/carry store. X9 survives every guard. -/
theorem arena_small_reservation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 1112#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (owned : ∀ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation →
      ArenaSmallReservationOwned s reservation) :
    ∃ fuel t, run fuel s = t ∧ ArenaSmallPost s t base address capacity used := by
  obtain ⟨fuel, u, hu, ⟨reached, result⟩, low⟩ :=
    arena_small_checks_runs s base address capacity used hc he ha hp
      headerBase headerCapacity headerUsed
  rcases result with failed | ⟨checks, upc, pointer, start, finish⟩
  · exact ⟨fuel, u, hu, reached.frame, Or.inl ⟨failed.1, failed.2, reached.memory⟩⟩
  · exact small_reservation_commit s u base address capacity used hc he ha reached upc
      pointer start finish (low upc) checks owned

end SszArm.NatAdd
