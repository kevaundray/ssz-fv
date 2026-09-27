import SszArm.NatDivisionArenaLayout
import SszArm.NatDivisionArenaCommit

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Both complete guard families execute to an actual failure or a committed
success. The successful intermediate state exposes the exact store image and
its independently proved physical frame, rather than postulating a branch. -/
def ArenaReservationPost (small : Bool) (s t : ArmState)
    (base address capacity used : BitVec 64) (words : Nat) : Prop :=
  (SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = none ∧
    read_pc t = base + 812#64 ∧ ArenaCheckpoint s t) ∨
  (SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words =
      some ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
        SszNative.Arena.finish address.toNat used.toNat words⟩ ∧
    ∃ u, ArenaCheckpoint s u ∧
      read_pc u = base + (if small then 752#64 else 284#64) ∧
      r (.GPR (if small then 8#5 else 10#5)) u = address ∧
      (r (.GPR (if small then 9#5 else 11#5)) u).toNat =
        SszNative.Arena.start address.toNat used.toNat ∧
      (r (.GPR (if small then 10#5 else 12#5)) u).toNat =
        SszNative.Arena.finish address.toNat used.toNat words ∧
      t = block base (if small then arenaSmallStoreOps else arenaBigStoreOps) u ∧
      read_pc t = base + (if small then 768#64 else 452#64) ∧
      (small = false → r (.GPR 8#5) t = r (.GPR 8#5) s))

/-- Full count-two reservation, with unrestricted old used and unsigned capacity. -/
theorem arena_small_reservation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 684#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 21#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ ArenaReservationPost true s t base address capacity used 2 := by
  obtain ⟨fuel, u, hu, reached, branch⟩ :=
    arena_small_checks_runs s base address capacity used hc he ha hp headerBase headerCapacity headerUsed
  rcases branch with failure | ⟨checks, upc, pointer, start, finish, count⟩
  · exact ⟨fuel, u, hu, Or.inl ⟨failure.1, failure.2, reached⟩⟩
  · let t := block base arenaSmallStoreOps u
    have ht := arena_small_store_run u base (reached.frame.code base hc)
      (reached.frame.error.trans he) (reached.frame.aligned ha) upc
    refine ⟨fuel + 4, t, ?_, Or.inr ⟨?_, u, reached, upc, pointer, start, finish, rfl, ?_, ?_⟩⟩
    · rw [run_plus, hu, ht]
    · exact (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) _).2 ⟨checks, rfl⟩
    · exact (arena_small_store_effect u base upc).1
    · intro impossible
      contradiction

theorem arena_big_reservation_checked_runs (s : ArmState) (base address capacity used : BitVec 64)
    (words : Nat) (positive : 0 < words) (layout : 8 * words < 2^63)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 220#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 21#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = used)
    (bytes : (r (.GPR 9#5) s).toNat = 8 * words) :
    ∃ fuel t, run fuel s = t ∧ ArenaReservationPost false s t base address capacity used words := by
  obtain ⟨fuel, u, hu, reached, branch⟩ :=
    arena_big_checks_runs s base address capacity used words positive layout hc he ha hp
      headerBase headerCapacity headerUsed bytes
  rcases branch with failure | ⟨checks, upc, pointer, start, finish, count⟩
  · exact ⟨fuel, u, hu, Or.inl ⟨failure.1, failure.2, reached⟩⟩
  · let t := block base arenaBigStoreOps u
    have ht := arena_big_store_run u base (reached.frame.code base hc)
      (reached.frame.error.trans he) (reached.frame.aligned ha) upc
    refine ⟨fuel + 4, t, ?_, Or.inr ⟨?_, u, reached, upc, pointer, start, finish, rfl, ?_, ?_⟩⟩
    · rw [run_plus, hu, ht]
    · exact (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ words positive _).2 ⟨checks, rfl⟩
    · exact (arena_big_store_effect u base).1
    · intro _
      exact (arena_big_store_registers u base 8#5 (by decide)).trans (count rfl)

private theorem arena_layout_header {s t : ArmState}
    (frame : Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t)
    (address : BitVec 64) (physical : address.toNat + 8 ≤ 2^64)
    (owned : Delimited.Protected [((r (.GPR 31#5) s).toNat - 16, 16)] address.toNat 8) :
    read_mem_bytes 8 address t = read_mem_bytes 8 address s := by
  have h := frame.load address.toNat 8 physical owned
  simpa [UintCodec.widthLoad, BitVec.ofNat_toNat, BitVec.toNat_inj] using h

/-- Complete large reservation from its first overflow instruction. Layout
failure never reads the descriptor. All other failures retain its original
bytes, and only the successful branch reaches the cursor commit. -/
theorem arena_big_reservation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 168#64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (positive : 0 < (r (.GPR 8#5) s).toNat)
    (headerBase : read_mem_bytes 8 (r (.GPR 21#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = used)
    (headerPhysical : ∀ offset ∈ [0#64, 8#64, 16#64],
      (r (.GPR 21#5) s + offset).toNat + 8 ≤ 2^64)
    (headerOwned : ∀ offset ∈ [0#64, 8#64, 16#64],
      Delimited.Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
        (r (.GPR 21#5) s + offset).toNat 8) :
    ∃ fuel t, run fuel s = t ∧
      ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
          (r (.GPR 8#5) s).toNat = none ∧ read_pc t = base + 812#64 ∧
        ArenaFrame s t ∧
        Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t) ∨
       (∃ u, ArenaFrame s u ∧
         Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s u ∧
         ArenaReservationPost false u t base address capacity used (r (.GPR 8#5) s).toNat ∧
         r (.GPR 8#5) u = r (.GPR 8#5) s)) := by
  obtain ⟨fuel, u, hu, frame, memory, count, branch⟩ :=
    arena_layout_checks_runs s base hc he ha hp hs
  rcases branch with ⟨failed, upc⟩ | ⟨layout, upc, bytes⟩
  · refine ⟨fuel, u, hu, Or.inl ⟨?_, upc, frame, memory⟩⟩
    apply (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ positive).2
    intro checks
    exact failed checks.1
  · have header : ∀ offset ∈ [0#64, 8#64, 16#64],
        read_mem_bytes 8 (r (.GPR 21#5) u + offset) u =
          read_mem_bytes 8 (r (.GPR 21#5) s + offset) s := by
      intro offset member
      rw [frame.registers 21#5 (by decide)]
      exact arena_layout_header memory _ (headerPhysical offset member) (headerOwned offset member)
    obtain ⟨more, t, ht, post⟩ := arena_big_reservation_checked_runs u base address capacity used
      (r (.GPR 8#5) s).toNat positive layout (frame.code base hc) (frame.error.trans he)
      (frame.aligned ha) upc
      (by simpa using (header 0#64 (by simp)).trans (by simpa using headerBase))
      ((header 8#64 (by simp)).trans headerCapacity)
      ((header 16#64 (by simp)).trans headerUsed) bytes
    refine ⟨fuel + more, t, ?_, Or.inr ⟨u, frame, memory, post, count⟩⟩
    rw [run_plus, hu, ht]

end SszArm.NatDivision
