import SszArm.NatMulReserveSize
import SszArm.NatMulReserveMemory

namespace SszArm.NatMul

/-- Ready for the original row loop at +580. All source values refer to the
physical state before allocation; initialized output is a proved conclusion. -/
structure ReserveReady (s t : ArmState) (base : BitVec 64)
    (reservation : SszNative.Arena.Reservation) (words : Nat) : Prop where
  pc : read_pc t = base + 580#64
  error : read_err t = .None
  program : t.program = s.program
  pointer : (r (.GPR 20#5) t).toNat = reservation.pointer
  total : (r (.GPR 19#5) t).toNat = words
  leftCount : r (.GPR 21#5) t = r (.GPR 21#5) s
  rightCount : r (.GPR 22#5) t = r (.GPR 22#5) s
  result : r (.GPR 24#5) t = r (.GPR 0#5) s
  left : r (.GPR 26#5) t = r (.GPR 1#5) s
  right : r (.GPR 27#5) t = r (.GPR 3#5) s
  payload : r (.GPR 28#5) t = r (.GPR 8#5) s
  rowEnd : r (.GPR 23#5) t = r (.GPR 21#5) s + r (.GPR 9#5) s
  rowNext : r (.GPR 25#5) t = r (.GPR 9#5) s + 1#64
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  x29 : r (.GPR 29#5) t = r (.GPR 29#5) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  cursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = BitVec.ofNat 64 reservation.used
  zero : UintCodec.WidthWords t (r (.GPR 20#5) t) (List.replicate words 0#64)
  zeroBytes : ∀ a : BitVec 64, reservation.pointer ≤ a.toNat →
    a.toNat < reservation.pointer + 8 * words → t.mem a = 0#8

/-- Five reserve checks, the cursor commitment, operand saves and the actual BL
plus runtime memset. Only initial physical storage/separation is required. -/
theorem reserve_allocation_runs (s : ArmState) (base address capacity used : BitVec 64)
    (words : Nat) (positive : 0 < words) (layout : 8 * words < 2^63)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 472#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (total : (r (.GPR 19#5) s).toNat = words)
    (bytes : (r (.GPR 2#5) s).toNat = 8 * words)
    (cursorPhysical : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64)
    (storage : address.toNat + capacity.toNat ≤ 2^64)
    (cursorSeparate : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words →
      (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ address.toNat + SszNative.Arena.start address.toNat used.toNat ∨
      address.toNat + SszNative.Arena.finish address.toNat used.toNat words ≤ (r (.GPR 5#5) s + 16#64).toNat) :
    ∃ fuel t, run fuel s = t ∧
      ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = none ∧
        read_pc t = base + 1076#64 ∧ t.mem = s.mem ∧ ReserveFrame s t) ∨
       ∃ reservation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = some reservation ∧
        ReserveReady s t base reservation words ∧
        Delimited.MemoryFrame [((r (.GPR 5#5) s + 16#64).toNat, 8),
          (reservation.pointer, 8 * words)] s t) := by
  obtain ⟨fuel, u, runU, checkpoint, failed | success⟩ :=
    reserve_checks_runs s base address capacity used words positive layout hc.body he ha hp
      headerBase headerCapacity headerUsed bytes
  · exact ⟨fuel, u, runU, Or.inl ⟨failed.1, failed.2, checkpoint.memory, checkpoint.frame⟩⟩
  · rcases success with ⟨checks, upc, addressReg, startReg, finishReg⟩
    let reservation : SszNative.Arena.Reservation :=
      ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
        SszNative.Arena.finish address.toNat used.toNat words⟩
    have reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words = some reservation :=
      (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ words positive reservation).2 ⟨checks, rfl⟩
    have finishBound := checks.2.2.2.2.2
    have payloadBound : reservation.pointer + 8 * words ≤ 2^64 := by
      dsimp [reservation]
      unfold SszNative.Arena.finish at finishBound
      omega
    have pointerBound : reservation.pointer < 2^64 := by omega
    have pointer : (r (.GPR 10#5) u + r (.GPR 11#5) u).toNat = reservation.pointer := by
      rw [addressReg, BitVec.toNat_add, startReg, Nat.mod_eq_of_lt pointerBound]
    have bytesU : (r (.GPR 2#5) u).toNat = 8 * words := by
      rw [checkpoint.frame.registers 2#5 (by decide)]
      exact bytes
    have r5 := checkpoint.frame.registers 5#5 (by decide)
    obtain ⟨more, t, runT, post⟩ := reserve_commit_zero_runs u base
      (hc.transport checkpoint.frame.program) (checkpoint.frame.error.trans he)
      (checkpoint.frame.aligned ha) upc (by rw [pointer, bytesU]; exact payloadBound)
    have output : (r (.GPR 20#5) t).toNat = reservation.pointer :=
      (congrArg BitVec.toNat post.pointer).trans pointer
    have separate : (r (.GPR 5#5) u + 16#64).toNat + 8 ≤ (r (.GPR 20#5) t).toNat ∨
        (r (.GPR 20#5) t).toNat + (r (.GPR 2#5) u).toNat ≤ (r (.GPR 5#5) u + 16#64).toNat := by
      rw [r5, output, bytesU]
      change (r (.GPR 5#5) s + 16#64).toNat + 8 ≤
          address.toNat + SszNative.Arena.start address.toNat used.toNat ∨
        address.toNat + SszNative.Arena.start address.toNat used.toNat + 8 * words ≤
          (r (.GPR 5#5) s + 16#64).toNat
      simpa only [SszNative.Arena.finish, Nat.add_assoc] using cursorSeparate checks
    have cursor := post.cursor (by rw [r5]; exact cursorPhysical) separate
    have finishWord : r (.GPR 12#5) u = BitVec.ofNat 64 reservation.used := by
      have finishNat : (r (.GPR 12#5) u).toNat = reservation.used := finishReg
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        congrArg (BitVec.ofNat 64) finishNat
    have scalar (reg : BitVec 5)
        (hg : reg ∉ [10#5, 11#5, 12#5, 13#5])
        (hz : reg ∉ [0#5, 1#5, 2#5, 3#5, 20#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5, 30#5]) :
        r (.GPR reg) t = r (.GPR reg) s :=
      (post.registers reg hz).trans (checkpoint.frame.registers reg hg)
    refine ⟨fuel + more, t, ?_, Or.inr ⟨reservation, reserved, ?_, ?_⟩⟩
    · rw [run_plus, runU, runT]
    · refine ⟨post.pc, post.error, post.program.trans checkpoint.frame.program, output,
        (congrArg BitVec.toNat (scalar 19#5 (by decide) (by decide))).trans total,
        scalar 21#5 (by decide) (by decide), scalar 22#5 (by decide) (by decide),
        post.result.trans (checkpoint.frame.registers 0#5 (by decide)),
        post.left.trans (checkpoint.frame.registers 1#5 (by decide)),
        post.right.trans (checkpoint.frame.registers 3#5 (by decide)),
        post.payload.trans (checkpoint.frame.registers 8#5 (by decide)), ?_, ?_,
        scalar 31#5 (by decide) (by decide), scalar 29#5 (by decide) (by decide), ?_, ?_, ?_, ?_⟩
      · rw [post.rowEnd, checkpoint.frame.registers 21#5 (by decide), checkpoint.frame.registers 9#5 (by decide)]
      · rw [post.rowNext, checkpoint.frame.registers 9#5 (by decide)]
      · intro reg nonzero
        exact (post.vectors reg nonzero).trans (checkpoint.frame.vectors reg)
      · simpa only [r5, finishWord] using cursor
      · exact post.words words bytesU (by rw [output]; exact payloadBound)
      · intro a low high
        exact post.zero_bytes a ⟨by rw [output]; exact low, by rw [output, bytesU]; exact high⟩
    · intro a outside
      have f := post.frame (by rw [r5]; exact cursorPhysical)
      rw [← checkpoint.memory]
      apply f a
      simpa only [r5, output, bytesU] using outside

theorem ReserveReady.rebase {s u t : ArmState} {base : BitVec 64}
    {reservation : SszNative.Arena.Reservation} {words : Nat}
    (post : ReserveReady u t base reservation words) (frame : ReserveSizeFrame s u) :
    ReserveReady s t base reservation words := by
  refine ⟨post.pc, post.error, post.program.trans frame.program, post.pointer, post.total,
    post.leftCount.trans (frame.registers 21#5 (by decide)),
    post.rightCount.trans (frame.registers 22#5 (by decide)),
    post.result.trans (frame.registers 0#5 (by decide)),
    post.left.trans (frame.registers 1#5 (by decide)),
    post.right.trans (frame.registers 3#5 (by decide)),
    post.payload.trans (frame.registers 8#5 (by decide)), ?_, ?_,
    post.sp.trans frame.sp, post.x29.trans (frame.registers 29#5 (by decide)),
    ?_, ?_, post.zero, post.zeroBytes⟩
  · rw [post.rowEnd, frame.registers 21#5 (by decide), frame.registers 9#5 (by decide)]
  · rw [post.rowNext, frame.registers 9#5 (by decide)]
  · intro reg nonzero
    exact (post.vectors reg nonzero).trans (frame.vectors reg)
  · simpa only [frame.registers 5#5 (by decide)] using post.cursor

/-- The entire original +412..+576 reservation path, including the helper return.
Exhaustion and success are classified, not preconditions. The only writes before
exhaustion are the real temporary stack spill. Successful allocation adds exactly
the cursor and the zero-filled output, never the already-used arena prefix. -/
theorem reserve_runs (s : ArmState) (base address capacity used : BitVec 64)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 412#64) (positive : 0 < reserveCount s)
    (stackPhysical : 16 ≤ (r (.GPR 31#5) s).toNat)
    (headerBase : read_mem_bytes 8 (r (.GPR 5#5) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s = used)
    (headerPhysical : (r (.GPR 5#5) s).toNat + 24 ≤ 2^64)
    (headerStack : (r (.GPR 5#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 5#5) s).toNat)
    (storage : address.toNat + capacity.toNat ≤ 2^64)
    (cursorSeparate : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat (reserveCount s) →
      (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ address.toNat + SszNative.Arena.start address.toNat used.toNat ∨
      address.toNat + SszNative.Arena.finish address.toNat used.toNat (reserveCount s) ≤
        (r (.GPR 5#5) s + 16#64).toNat) :
    ∃ fuel t, run fuel s = t ∧
      ((((2^64 ≤ reserveCount s ∧ read_pc t = base + 1344#64) ∨
         (SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (reserveCount s) = none ∧
           read_pc t = base + 1076#64)) ∧
        (∃ u, ReserveSizeFrame s u ∧ ReserveFrame u t) ∧
        Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t) ∨
       ∃ reservation,
        SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (reserveCount s) = some reservation ∧
        ReserveReady s t base reservation (reserveCount s) ∧
        Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16),
          ((r (.GPR 5#5) s + 16#64).toNat, 8), (reservation.pointer, 8 * reserveCount s)] s t) := by
  obtain ⟨fuel, u, runU, frame, memory, overflow | badLayout | layout⟩ :=
    reserve_size_runs s base hc.body he ha hp stackPhysical
  · exact ⟨fuel, u, runU, Or.inl ⟨Or.inl overflow, ⟨u, frame, ReserveFrame.refl u⟩, memory⟩⟩
  · have exhausted : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (reserveCount s) = none :=
      (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ positive).2 (fun checks => badLayout.1 checks.1)
    exact ⟨fuel, u, runU, Or.inl ⟨Or.inr ⟨exhausted, badLayout.2⟩,
      ⟨u, frame, ReserveFrame.refl u⟩, memory⟩⟩
  · have r5 := frame.registers 5#5 (by decide)
    have header (offset : BitVec 64) (ho : offset = 0#64 ∨ offset = 8#64 ∨ offset = 16#64) :
        read_mem_bytes 8 (r (.GPR 5#5) u + offset) u =
          read_mem_bytes 8 (r (.GPR 5#5) s + offset) s := by
      rw [r5]
      apply memory.read
      · rcases ho with rfl | rfl | rfl <;> bv_omega
      · right
        intro span member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst span
        rcases ho with rfl | rfl | rfl <;> bv_omega
    have baseU : read_mem_bytes 8 (r (.GPR 5#5) u) u = address := by
      simpa using (header 0#64 (Or.inl rfl)).trans (by simpa using headerBase)
    have capacityU := (header 8#64 (Or.inr (Or.inl rfl))).trans headerCapacity
    have usedU := (header 16#64 (Or.inr (Or.inr rfl))).trans headerUsed
    obtain ⟨more, t, runT, failed | success⟩ :=
      reserve_allocation_runs u base address capacity used (reserveCount s) positive layout.1
        (hc.transport frame.program) (frame.error.trans he) (frame.aligned ha) layout.2.1
        baseU capacityU usedU layout.2.2.1 layout.2.2.2
        (by rw [r5]; bv_omega) storage (by rw [r5]; exact cursorSeparate)
    · refine ⟨fuel + more, t, ?_, Or.inl ⟨Or.inr ⟨failed.1, failed.2.1⟩,
        ⟨u, frame, failed.2.2.2⟩, ?_⟩⟩
      · rw [run_plus, runU, runT]
      · intro a outside
        rw [failed.2.2.1]
        exact memory a outside
    · rcases success with ⟨reservation, reserved, ready, writes⟩
      refine ⟨fuel + more, t, ?_, Or.inr ⟨reservation, reserved, ready.rebase frame, ?_⟩⟩
      · rw [run_plus, runU, runT]
      · intro a outside
        have outsideCursor : ∀ span ∈ [((r (.GPR 5#5) u + 16#64).toNat, 8),
            (reservation.pointer, 8 * reserveCount s)],
            a.toNat < span.1 ∨ span.1 + span.2 ≤ a.toNat := by
          intro span member
          apply outside span
          simpa only [r5] using List.mem_cons_of_mem ((r (.GPR 31#5) s).toNat - 16, 16) member
        exact (writes a outsideCursor).trans
          (memory a (fun span member => outside span (List.mem_cons.mpr (Or.inl (by simpa using member)))))

/-- The checked native model has the same failure and successful reservation
branches; the parent row-loop proof supplies the already-fixed writtenWords. -/
theorem reserve_model_failure (left right : SszNative.NatOperand)
    (address capacity used : Nat) (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (failed : 2^64 ≤ left.wordCount + right.wordCount ∨
      SszNative.Arena.reserve address capacity used (left.wordCount + right.wordCount) = none) :
    SszNative.NatMul.run left right address capacity used =
      SszNative.NatArithmetic.unchanged used (.error .scratchExhausted) := by
  rw [SszNative.NatMul.run_large left right address capacity used hl hr]
  rcases failed with overflow | exhausted
  · rw [if_neg (by omega)]
  · split <;> simp only [exhausted]

theorem reserve_model_success (left right : SszNative.NatOperand)
    (address capacity used : Nat) (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (reservation : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address capacity used (left.wordCount + right.wordCount) = some reservation) :
    SszNative.NatMul.run left right address capacity used =
      SszNative.NatArithmetic.committed reservation (SszNative.NatMul.writtenWords left right) := by
  have checks := ((SszNative.Arena.reserve_eq_some_iff_checks address capacity used
    (left.wordCount + right.wordCount) (by omega) reservation).1 reserved).1
  rw [SszNative.NatMul.run_large left right address capacity used hl hr, if_pos (by have := checks.1; omega), reserved]

end SszArm.NatMul
