import SszArm.NatAddArenaCommit
import SszArm.NatAddArenaLayout
import SszArm.NatAddContract

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def arenaCursorMemory (s : ArmState) (reservation : SszNative.Arena.Reservation) : ArmState :=
  write_mem_bytes 8 (r (.GPR 5#5) s + 16#64) (BitVec.ofNat 64 reservation.used) s

structure ArenaBigSuccess (s t : ArmState) (base : BitVec 64)
    (reservation : SszNative.Arena.Reservation) : Prop where
  pc : read_pc t = base + 276#64
  pointer : (r (.GPR 9#5) t).toNat = reservation.pointer
  used : r (.GPR 11#5) t = BitVec.ofNat 64 reservation.used
  cursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = BitVec.ofNat 64 reservation.used
  memory : t.mem = (arenaCursorMemory s reservation).mem
  frame : Delimited.MemoryFrame [((r (.GPR 5#5) s + 16#64).toNat, 8)] s t
  width : r (.GPR 8#5) t = r (.GPR 8#5) s
  allocation : r (.GPR 10#5) t = r (.GPR 9#5) t

def ArenaBigPost (s t : ArmState) (base address capacity used : BitVec 64)
    (words : Nat) : Prop :=
  ArenaFrame s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = none ∧
        read_pc t = base + 1248#64 ∧ t.mem = s.mem) ∨
      ∃ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = some reservation ∧
        ArenaBigSuccess s t base reservation)

private theorem arena_word_eq (word : BitVec 64) (value : Nat) (h : word.toNat = value) :
    word = BitVec.ofNat 64 value := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The dynamic-size checked allocator commits precisely its cursor on success,
with no capacity-isize hypothesis and no mutation on any failed arena guard. -/
theorem arena_big_reservation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (words : Nat) (positive : 0 < words) (layout : 8 * words < 2^63)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 204#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (bytes : (r (.GPR 11#5) s).toNat = 8 * words)
    (cursorPhysical : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64) :
    ∃ fuel t, run fuel s = t ∧ ArenaBigPost s t base address capacity used words := by
  obtain ⟨fuel, u, hu, ⟨reached, result⟩, preserved⟩ :=
    arena_big_checks_runs s base address capacity used words positive layout hc he ha hp
      headerBase headerCapacity headerUsed bytes
  rcases result with failed | successful
  · exact ⟨fuel, u, hu, reached.frame, Or.inl ⟨failed.1, failed.2, reached.memory⟩⟩
  · rcases successful with ⟨checks, upc, pointerReg, startReg, finishReg⟩
    have preserved := preserved upc
    let reservation : SszNative.Arena.Reservation :=
      ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
        SszNative.Arena.finish address.toNat used.toNat words⟩
    have success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = some reservation :=
      (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ words positive reservation).2 ⟨checks, rfl⟩
    have pointerBound : reservation.pointer < 2^64 := by
      have bounds := SszNative.Arena.aligned_bounds (address.toNat + used.toNat)
      have pointerEq := SszNative.Arena.start_pointer address.toNat used.toNat
      have rounding := checks.2.2.1
      dsimp [reservation]
      omega
    have pointer : (r (.GPR 9#5) u + r (.GPR 12#5) u).toNat = reservation.pointer := by
      rw [pointerReg, BitVec.toNat_add, startReg, Nat.mod_eq_of_lt pointerBound]
    have finishWord : r (.GPR 11#5) u = BitVec.ofNat 64 reservation.used :=
      arena_word_eq _ _ finishReg
    have r5 := reached.frame.registers 5#5 (by decide)
    let t := block base arenaBigStoreOps u
    have effect := arena_big_store_effect u base upc
    have memory := arena_big_store_memory u base (by rw [r5]; exact cursorPhysical) upc
    have hrun := arena_big_store_run u base (reached.frame.code base hc)
      (reached.frame.error.trans he) (reached.frame.aligned ha) upc
    have exactMemory : (arenaBigMemory u).mem = (arenaCursorMemory s reservation).mem := by
      unfold arenaBigMemory arenaCursorMemory
      rw [r5, finishWord]
      exact mem_write_mem_bytes_of_mem_eq reached.memory _ _ _
    refine ⟨fuel + 2, t, ?_, reached.frame.trans (arena_big_store_frame u base),
      Or.inr ⟨reservation, success, ?_⟩⟩
    · rw [run_plus, hu, hrun]
    · refine ⟨effect.1, ?_, effect.2.2.1.trans finishWord, ?_, effect.2.2.2.trans exactMemory, ?_, ?_, ?_⟩
      · rw [effect.2.1]
        exact pointer
      · rw [← r5]
        exact memory.2.trans finishWord
      · intro a outside
        rw [← reached.memory]
        exact memory.1 a (by simpa only [r5] using outside)
      · have same : r (.GPR 8#5) t = r (.GPR 8#5) u := by
          simp [t, arenaBigStoreOps, block, Op.effect, put, next, state_simp_rules]
        exact same.trans preserved.1
      · have same : r (.GPR 10#5) t = r (.GPR 10#5) u := by
          simp [t, arenaBigStoreOps, block, Op.effect, put, next, state_simp_rules]
        apply BitVec.eq_of_toNat_eq
        rw [same, effect.2.1, pointer]
        exact preserved.2

/-- The full positive-length layout and allocator prefix; failure may change
only the real lowering spill, success additionally changes the cursor word. -/
def ArenaBigLayoutPost (s t : ArmState) (base address capacity used : BitVec 64) : Prop :=
  ArenaFrame s t ∧
    ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
          ((r (.GPR 8#5) s).toNat + 1) = none ∧
        read_pc t = base + 1248#64 ∧
        Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t) ∨
      ∃ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
          ((r (.GPR 8#5) s).toNat + 1) = some reservation ∧
        read_pc t = base + 276#64 ∧
        (r (.GPR 9#5) t).toNat = reservation.pointer ∧
        r (.GPR 11#5) t = BitVec.ofNat 64 reservation.used ∧
        read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = BitVec.ofNat 64 reservation.used ∧
        Delimited.MemoryFrame
          [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 5#5) s + 16#64).toNat, 8)] s t ∧
        r (.GPR 8#5) t = r (.GPR 8#5) s ∧
        r (.GPR 10#5) t = r (.GPR 9#5) t)

/-- Entry at +144 executes both native layout guards, the spill/restore,
all arena arithmetic guards, and the cursor commitment. -/
theorem arena_big_layout_reservation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 144#64) (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (headerPhysical : (r (.GPR 5#5) s).toNat + 24 ≤ 2^64)
    (headerSeparate : (r (.GPR 5#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 5#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ ArenaBigLayoutPost s t base address capacity used := by
  obtain ⟨fuel, u, hu, frame, memory, r8, failed | success⟩ :=
    arena_layout_checks_runs s base hc he ha hp hs
  · refine ⟨fuel, u, hu, frame, Or.inl ⟨?_, failed.2, memory⟩⟩
    apply (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by omega)).2
    intro checks
    exact failed.1 checks.1
  · have r5 := frame.registers 5#5 (by decide)
    have header (offset : BitVec 64) (ho : offset = 0#64 ∨ offset = 8#64 ∨ offset = 16#64) :
        read_mem_bytes 8 (r (.GPR 5#5) u + offset) u =
          read_mem_bytes 8 (r (.GPR 5#5) s + offset) s := by
      rw [r5]
      apply memory.read
      · rcases ho with rfl | rfl | rfl <;> bv_omega
      · right
        intro span hspan
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hspan
        subst span
        rcases ho with rfl | rfl | rfl <;> bv_omega
    have baseU : read_mem_bytes 8 (r (.GPR 5#5) u) u = address := by
      simpa using (header 0#64 (Or.inl rfl)).trans (by simpa using headerBase)
    have capU := (header 8#64 (Or.inr (Or.inl rfl))).trans headerCapacity
    have usedU := (header 16#64 (Or.inr (Or.inr rfl))).trans headerUsed
    obtain ⟨more, t, ht, allocatorFrame, failed | committed⟩ :=
      arena_big_reservation_runs u base address capacity used ((r (.GPR 8#5) s).toNat + 1)
        (by omega) success.1 (frame.code base hc) (frame.error.trans he)
        (frame.aligned ha) success.2.1 baseU capU usedU success.2.2
        (by rw [r5]; bv_omega)
    · refine ⟨fuel + more, t, ?_, frame.trans allocatorFrame, Or.inl ⟨failed.1, failed.2.1, ?_⟩⟩
      · rw [run_plus, hu, ht]
      · intro a outside
        rw [failed.2.2]
        exact memory a outside
    · rcases committed with ⟨reservation, reserved, post⟩
      refine ⟨fuel + more, t, ?_, frame.trans allocatorFrame,
        Or.inr ⟨reservation, reserved, post.pc, post.pointer, post.used, ?_, ?_,
          post.width.trans r8, post.allocation⟩⟩
      · rw [run_plus, hu, ht]
      · simpa only [r5] using post.cursor
      · intro a outside
        have cursorOutside : ∀ span ∈ [((r (.GPR 5#5) u + 16#64).toNat, 8)],
            a.toNat < span.1 ∨ span.1 + span.2 ≤ a.toNat := by
          intro span member
          apply outside span
          simpa only [r5] using List.mem_cons_of_mem ((r (.GPR 31#5) s).toNat - 16, 16) member
        exact (post.frame a cursorOutside).trans
          (memory a (fun span member => outside span (List.mem_cons.mpr (Or.inl (by simpa using member)))))

end SszArm.NatAdd
