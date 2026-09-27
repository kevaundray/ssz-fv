import SszArm.DelimitedArenaChecks
import SszArm.DelimitedArenaCommit
import SszDelimitedProofs

namespace SszArm.Delimited

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private def ArenaCheckKind.entry : ArenaCheckKind → BitVec 64
  | .address => 268#64
  | .rounding => 284#64
  | .alignment => 292#64
  | .ending => 312#64
  | .capacity => 320#64

private def ArenaCheckKind.steps : ArenaCheckKind → Nat
  | .address => 4
  | .rounding => 2
  | .alignment => 5
  | .ending => 2
  | .capacity => 4

private def ArenaCheckKind.clobbers : ArenaCheckKind → List (BitVec 5)
  | .address => [8#5, 9#5, 10#5]
  | .rounding => []
  | .alignment => [9#5, 10#5, 11#5]
  | .ending => []
  | .capacity => [10#5, 11#5]

private theorem arena_guard_registers (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) (reg : BitVec 5) (hr : reg ∉ kind.clobbers) :
    r (.GPR reg) (block base kind.ops s) = r (.GPR reg) s := by
  cases kind <;> simp only [ArenaCheckKind.clobbers, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hr <;>
    simp (disch := simp_all) [ArenaCheckKind.ops, arenaAddressOps, arenaRoundOps,
      arenaAlignOps, arenaEndOps, arenaCapacityOps, block, Op.effect, put, next,
      state_simp_rules]

private theorem arena_guard_frame (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) : ArenaFrame s (block base kind.ops s) := by
  have hf := (arena_check_frame kind s base).1
  refine ⟨hf.program, hf.error, ?_, hf.vectors⟩
  intro reg hr
  apply arena_guard_registers kind s base reg
  cases kind <;> simp_all [ArenaCheckKind.clobbers]

private theorem arena_guard_run (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + kind.entry) :
    run kind.steps s = block base kind.ops s := by
  cases kind with
  | address => exact arenaAddress_run s base hc he ha hp
  | rounding => exact arenaRound_run s base hc he ha hp
  | alignment => exact arenaAlign_run s base hc he ha hp
  | ending => exact arenaEnd_run s base hc he ha hp
  | capacity => exact arenaCapacity_run s base hc he ha hp

/-- A read-only checkpoint records actual execution, not a symbolic guard
assumption. All five failure branches can return this unchanged memory. -/
private structure ArenaCheckpoint (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : ArenaFrame s t
  memory : t.mem = s.mem

private theorem ArenaCheckpoint.refl (s : ArmState) : ArenaCheckpoint s s :=
  ⟨⟨0, rfl⟩, ArenaFrame.refl s, rfl⟩

private theorem ArenaCheckpoint.step {s t : ArmState} (reached : ArenaCheckpoint s t)
    (kind : ArenaCheckKind) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + kind.entry) :
    ArenaCheckpoint s (block base kind.ops t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := arena_guard_run kind t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨⟨fuel + kind.steps, ?_⟩,
    reached.frame.trans (arena_guard_frame kind t base),
    (arena_check_frame kind t base).2.trans reached.memory⟩
  rw [run_plus, hr, hrun]

private theorem ArenaCheckpoint.header {s t : ArmState} (reached : ArenaCheckpoint s t)
    (offset : BitVec 64) :
    read_mem_bytes 8 (r (.GPR 4#5) t + offset) t =
      read_mem_bytes 8 (r (.GPR 4#5) s + offset) s := by
  rw [reached.frame.registers 4#5 (by decide)]
  exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.memory _ _

/-- Exactly the two writable intervals; padding and the used prefix stay read-only. -/
def arenaReservationWrites (s : ArmState) (reservation : SszNative.Arena.Reservation) : List Span :=
  [((r (.GPR 4#5) s + 16#64).toNat, 8), (reservation.pointer, 16)]

/-- Ownership is required only when the native guards permit a commit. Unlike
Arena.Valid, this imposes no isize bound on the arena capacity or used cursor.
Read-only input/cap limbs may alias each other or the used arena prefix. -/
def ArenaReservationOwned (s : ArmState) (reservation : SszNative.Arena.Reservation) : Prop :=
  (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ 2^64 ∧
  0 < reservation.pointer ∧ reservation.pointer + 16 ≤ 2^64 ∧
  ((r (.GPR 4#5) s + 16#64).toNat + 8 ≤ reservation.pointer ∨
    reservation.pointer + 16 ≤ (r (.GPR 4#5) s + 16#64).toNat)

/-- Ordinary physical caller storage discharges commit ownership without the
unnecessary capacity-isize clause of Arena.Valid. Even an invalid initial used
cursor is permitted: the exact native guards decide whether it can succeed. -/
theorem arena_reservation_owned_of_storage (s : ArmState)
    (address capacity used : BitVec 64) (reservation : SszNative.Arena.Reservation)
    (positive : 0 < address.toNat)
    (physical : address.toNat + capacity.toNat ≤ 2^64)
    (cursor : (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ 2^64)
    (separate : (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ address.toNat ∨
      address.toNat + capacity.toNat ≤ (r (.GPR 4#5) s + 16#64).toNat)
    (success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation) :
    ArenaReservationOwned s reservation := by
  obtain ⟨pointerPositive, _, lower, ending, fits, pointerPhysical⟩ :=
    SszNative.Delimited.reservation_bounds address.toNat capacity.toNat used.toNat
      physical (fun _ => positive) reservation success
  refine ⟨cursor, pointerPositive, pointerPhysical, ?_⟩
  omega

def arenaReservedMemory (s : ArmState) (reservation : SszNative.Arena.Reservation) : ArmState :=
  write_mem_bytes 16 (BitVec.ofNat 64 reservation.pointer)
    (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
    (write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (BitVec.ofNat 64 reservation.used) s)

structure ArenaReservationSuccess (s t : ArmState) (base : BitVec 64)
    (count : Nat) (reservation : SszNative.Arena.Reservation) : Prop where
  pc : read_pc t = base + 352#64
  pointer : (r (.GPR 20#5) t).toNat = reservation.pointer
  words : r (.GPR 19#5) t = 2#64
  cursor : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t = BitVec.ofNat 64 reservation.used
  memory : t.mem = (arenaReservedMemory s reservation).mem
  frame : MemoryFrame (arenaReservationWrites s reservation) s t
  pair : SszNative.NatMemory.Pair (widthLoad t) (r (.GPR 20#5) t) (r (.GPR 19#5) t) count

/-- The outcome exposes the exact reserve result and stops before either error
reporting or the Option discriminant load. -/
def ArenaReservationPost (s t : ArmState) (base address capacity used : BitVec 64)
    (count : Nat) : Prop :=
  ArenaFrame s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none ∧
        read_pc t = base + 752#64 ∧ t.mem = s.mem) ∨
      ∃ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation ∧
        ArenaReservationSuccess s t base count reservation)

private theorem arena_reservation_failure (s t : ArmState)
    (base address capacity used : BitVec 64) (count : Nat)
    (reached : ArenaCheckpoint s t) (hp : read_pc t = base + 752#64)
    (failed : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2) :
    ∃ fuel t, run fuel s = t ∧ ArenaReservationPost s t base address capacity used count := by
  obtain ⟨fuel, hr⟩ := reached.runs
  exact ⟨fuel, t, hr, reached.frame, Or.inl
    ⟨(SszNative.Arena.reserve_eq_none_iff_checks _ _ _ 2 (by decide)).2 failed,
      hp, reached.memory⟩⟩

private theorem arena_word_eq (word : BitVec 64) (value : Nat) (h : word.toNat = value) :
    word = BitVec.ofNat 64 value := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem arena_reservation_commit (s u : ArmState)
    (base address capacity used : BitVec 64) (count : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (reached : ArenaCheckpoint s u) (hp : read_pc u = base + 336#64)
    (h8 : r (.GPR 8#5) u = address)
    (h9 : (r (.GPR 9#5) u).toNat = SszNative.Arena.start address.toNat used.toNat)
    (h10 : (r (.GPR 10#5) u).toNat = SszNative.Arena.finish address.toNat used.toNat 2)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 2)
    (owned : ∀ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation →
      ArenaReservationOwned s reservation)
    (low : (r (.GPR 24#5) s).toNat = count % 2^64)
    (high : (r (.GPR 23#5) s).toNat = count / 2^64) :
    ∃ fuel t, run fuel s = t ∧ ArenaReservationPost s t base address capacity used count := by
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
  have pointer : (arenaCommitPointer u).toNat = reservation.pointer := by
    unfold arenaCommitPointer
    rw [h8, BitVec.toNat_add, h9, Nat.mod_eq_of_lt pointerBound]
  have pointerWord := arena_word_eq _ _ pointer
  have finishWord : r (.GPR 10#5) u = BitVec.ofNat 64 reservation.used := arena_word_eq _ _ h10
  have r4 := reached.frame.registers 4#5 (by decide)
  have r23 := reached.frame.registers 23#5 (by decide)
  have r24 := reached.frame.registers 24#5 (by decide)
  have aligned : reservation.pointer % 8 = 0 := by
    dsimp [reservation]
    rw [SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  have commitOwned : ArenaCommitOwned u := by
    unfold ArenaCommitOwned
    rw [pointer, r4]
    exact ⟨ho.1, ho.2.1, aligned, ho.2.2.1, ho.2.2.2⟩
  let t := block base arenaStoreOps u
  have effect := arena_store_effect u base hp
  have memory := arena_store_memory u base commitOwned hp
  have writes : arenaCommitWrites u = arenaReservationWrites s reservation := by
    simp only [arenaCommitWrites, arenaReservationWrites, pointer, r4]
  have exactMemory : (arenaCommitMemory u).mem = (arenaReservedMemory s reservation).mem := by
    unfold arenaCommitMemory arenaReservedMemory
    rw [pointerWord, finishWord, r4, r23, r24]
    apply mem_write_mem_bytes_of_mem_eq
    exact mem_write_mem_bytes_of_mem_eq reached.memory _ _ _
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := arenaStore_run u base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨fuel + 4, t, ?_, reached.frame.trans (arena_store_frame u base),
    Or.inr ⟨reservation, success, ?_⟩⟩
  · rw [run_plus, hr, hrun]
  · refine ⟨effect.1, ?_, effect.2.2.1, ?_, effect.2.2.2.trans exactMemory, ?_, ?_⟩
    · rw [effect.2.1]
      exact pointer
    · rw [← r4]
      exact memory.2.1.trans finishWord
    · intro a outside
      rw [← reached.memory]
      exact memory.1 a (by simpa only [writes] using outside)
    · rw [effect.2.1, effect.2.2.1]
      have value : (r (.GPR 24#5) u).toNat + 2^64 * (r (.GPR 23#5) u).toNat = count := by
        rw [r24, r23, low, high]
        omega
      rw [← value]
      exact memory.2.2

/-- Actual entry-to-exit refinement of PCs 268..348. Every arithmetic guard is
executed and classified, including overflow and capacity failure. Success
commits exactly two limbs even when the later Option limit is None. The only
storage assumptions concern physical bytes that a successful path writes. -/
theorem arena_reservation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (count : Nat) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 268#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 4#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s = used)
    (countRange : 2^64 ≤ count ∧ count < 2^67)
    (low : (r (.GPR 24#5) s).toNat = count % 2^64)
    (high : (r (.GPR 23#5) s).toNat = count / 2^64)
    (owned : ∀ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation →
      ArenaReservationOwned s reservation) :
    ∃ fuel t, run fuel s = t ∧ ArenaReservationPost s t base address capacity used count := by
  let a := block base arenaAddressOps s
  have ra : ArenaCheckpoint s a := (ArenaCheckpoint.refl s).step .address base hc he ha hp
  have ea := arena_address_exit s base
  simp only [headerBase, headerUsed] at ea
  by_cases addressOK : address.toNat + used.toNat < 2^64
  · have apc : read_pc a = base + 284#64 := by
      exact ea.2.2.2.trans (if_neg (by omega))
    have addressNat : (r (.GPR 10#5) a).toNat = address.toNat + used.toNat := by
      rw [ea.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base arenaRoundOps a
    have rb : ArenaCheckpoint s b := ra.step .rounding base hc he ha apc
    have eb := arena_round_exit a base
    have b8 : r (.GPR 8#5) b = address :=
      (arena_guard_registers .rounding a base 8#5 (by decide)).trans ea.1
    have b9 : r (.GPR 9#5) b = used :=
      (arena_guard_registers .rounding a base 9#5 (by decide)).trans ea.2.1
    have b10 : r (.GPR 10#5) b = r (.GPR 10#5) a :=
      arena_guard_registers .rounding a base 10#5 (by decide)
    by_cases roundOK : address.toNat + used.toNat + 7 < 2^64
    · have bpc : read_pc b = base + 292#64 := by
        rw [addressNat] at eb
        exact eb.trans (if_neg (by omega))
      have padding := (reservation_padding (r (.GPR 10#5) b)
        (by rw [b10, addressNat]; exact roundOK)).2
      rw [b10, addressNat] at padding
      let c := block base arenaAlignOps b
      have rc : ArenaCheckpoint s c := rb.step .alignment base hc he ha bpc
      have ec := arena_align_exit b base
      have c8 : r (.GPR 8#5) c = address :=
        (arena_guard_registers .alignment b base 8#5 (by decide)).trans b8
      have padding' : (((r (.GPR 10#5) b + 7#64) &&& 18446744073709551608#64) -
          r (.GPR 10#5) b).toNat = SszNative.Arena.padding (address.toNat + used.toNat) := by
        simpa only [b10] using padding
      by_cases startOK : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have cpc : read_pc c = base + 312#64 := by
          have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_neg (by unfold SszNative.Arena.start at startOK; omega))
        have startNat : (r (.GPR 9#5) c).toNat = SszNative.Arena.start address.toNat used.toNat := by
          rw [ec.2.2.1, BitVec.toNat_add, padding', b9]
          unfold SszNative.Arena.start at *
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        let d := block base arenaEndOps c
        have rd : ArenaCheckpoint s d := rc.step .ending base hc he ha cpc
        have ed := arena_end_exit c base
        have d8 : r (.GPR 8#5) d = address :=
          (arena_guard_registers .ending c base 8#5 (by decide)).trans c8
        have d9 : (r (.GPR 9#5) d).toNat = SszNative.Arena.start address.toNat used.toNat :=
          (congrArg BitVec.toNat
            (arena_guard_registers .ending c base 9#5 (by decide))).trans startNat
        by_cases finishOK : SszNative.Arena.finish address.toNat used.toNat 2 < 2^64
        · have dpc : read_pc d = base + 320#64 := by
            rw [startNat] at ed
            exact ed.trans (if_neg (by unfold SszNative.Arena.finish at finishOK; omega))
          let e := block base arenaCapacityOps d
          have re : ArenaCheckpoint s e := rd.step .capacity base hc he ha dpc
          have ee := arena_capacity_exit d base
          have capLoad : read_mem_bytes 8 (r (.GPR 4#5) d + 8#64) d = capacity :=
            (rd.header 8#64).trans headerCapacity
          have finishNat : (r (.GPR 9#5) d + 16#64).toNat =
              SszNative.Arena.finish address.toNat used.toNat 2 := by
            rw [BitVec.toNat_add, d9]
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt finishOK
          by_cases fits : SszNative.Arena.finish address.toNat used.toNat 2 ≤ capacity.toNat
          · have epc : read_pc e = base + 336#64 := by
              have hepc := ee.2.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_neg (by omega))
            apply arena_reservation_commit s e base address capacity used count hc he ha re epc
            · exact (arena_guard_registers .capacity d base 8#5 (by decide)).trans d8
            · exact (congrArg BitVec.toNat
                (arena_guard_registers .capacity d base 9#5 (by decide))).trans d9
            · rw [ee.2.1]
              exact finishNat
            · exact ⟨by decide, addressOK, roundOK, startOK, finishOK, fits⟩
            · exact owned
            · exact low
            · exact high
          · apply arena_reservation_failure s e base address capacity used count re
            · have hepc := ee.2.2
              rw [capLoad, finishNat] at hepc
              exact hepc.trans (if_pos (by omega))
            · intro checks
              exact fits checks.2.2.2.2.2
        · apply arena_reservation_failure s d base address capacity used count rd
          · rw [startNat] at ed
            exact ed.trans (if_pos (by unfold SszNative.Arena.finish at finishOK; omega))
          · intro checks
            exact finishOK checks.2.2.2.2.1
      · apply arena_reservation_failure s c base address capacity used count rc
        · have hcpc := ec.2.2.2
          rw [padding', b9] at hcpc
          exact hcpc.trans (if_pos (by unfold SszNative.Arena.start at startOK; omega))
        · intro checks
          exact startOK checks.2.2.2.1
    · apply arena_reservation_failure s b base address capacity used count rb
      · rw [addressNat] at eb
        exact eb.trans (if_pos (by omega))
      · intro checks
        exact roundOK checks.2.2.1
  · apply arena_reservation_failure s a base address capacity used count ra
    · exact ea.2.2.2.trans (if_pos (by omega))
    · intro checks
      exact addressOK checks.2.1

/-- The two distinct exits are an iff classification of the pure allocator,
not merely a success-path implication. -/
theorem ArenaReservationPost.failure_iff {s t : ArmState}
    {base address capacity used : BitVec 64} {count : Nat}
    (post : ArenaReservationPost s t base address capacity used count) :
    read_pc t = base + 752#64 ↔
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none := by
  rcases post.2 with failed | ⟨reservation, successful, effect⟩
  · exact ⟨fun _ => failed.1, fun _ => failed.2.1⟩
  · have different : base + 352#64 ≠ base + 752#64 := by bv_omega
    simp only [effect.pc, successful, different, Option.some_ne_none]

theorem ArenaReservationPost.success_iff {s t : ArmState}
    {base address capacity used : BitVec 64} {count : Nat}
    (post : ArenaReservationPost s t base address capacity used count) :
    read_pc t = base + 352#64 ↔
      ∃ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation := by
  rcases post.2 with failed | ⟨reservation, successful, effect⟩
  · have different : base + 752#64 ≠ base + 352#64 := by bv_omega
    simp [failed.1, failed.2.1, different]
  · exact ⟨fun _ => ⟨reservation, successful⟩, fun _ => effect.pc⟩

end SszArm.Delimited
