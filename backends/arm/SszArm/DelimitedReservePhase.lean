import SszArm.DelimitedPrepared
import SszArm.DelimitedArena
import SszArm.DelimitedTails

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem reserve_limit_register (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (unchanged : reg ≠ 8#5) :
    r (.GPR reg) (block base largeLimitOps s) = r (.GPR reg) s := by
  simp [largeLimitOps, block, Op.effect, put, next, state_simp_rules, unchanged]

private theorem reserve_limit_vectors (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (block base largeLimitOps s) = r (.SFP reg) s := by
  simp [largeLimitOps, block, Op.effect, put, next, state_simp_rules]

/-- Observe the real paired store in the checked reservation memory image.
The payload is not inferred merely from the numeric Nat relation. -/
private theorem reservation_stored_words (s t : ArmState)
    (reservation : SszNative.Arena.Reservation)
    (physical : reservation.pointer + 16 ≤ 2^64)
    (memory : t.mem = (arenaReservedMemory s reservation).mem) :
    widthLoad t reservation.pointer 8 = some (r (.GPR 24#5) s).toNat ∧
      widthLoad t (reservation.pointer + 8) 8 = some (r (.GPR 23#5) s).toNat := by
  let pointer := BitVec.ofNat 64 reservation.pointer
  have pointerNat : pointer.toNat = reservation.pointer := by
    change reservation.pointer % 2^64 = reservation.pointer
    exact Nat.mod_eq_of_lt (by omega)
  have second : BitVec.ofNat 64 (reservation.pointer + 8) = pointer + 8#64 := by
    simp [pointer, BitVec.ofNat_add]
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  let cursorState := write_mem_bytes 8 (r (.GPR 4#5) s + 16#64)
    (BitVec.ofNat 64 reservation.used) s
  have paired := UintCodec.Tail.write_pair_words cursorState pointer
    (r (.GPR 24#5) s) (r (.GPR 23#5) s) (by rw [pointerNat]; exact physical)
  change some (read_mem_bytes 8 pointer t).toNat = _ ∧
    some (read_mem_bytes 8 (BitVec.ofNat 64 (reservation.pointer + 8)) t).toNat = _
  rw [reads 8 pointer, reads 8 (BitVec.ofNat 64 (reservation.pointer + 8)), second]
  change some (read_mem_bytes 8 pointer
      (write_mem_bytes 16 pointer (r (.GPR 23#5) s ++ r (.GPR 24#5) s) cursorState)).toNat = _ ∧
    some (read_mem_bytes 8 (pointer + 8#64)
      (write_mem_bytes 16 pointer (r (.GPR 23#5) s ++ r (.GPR 24#5) s) cursorState)).toNat = _
  rw [paired]
  constructor
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 pointer (pointer + 8#64)
      (r (.GPR 23#5) s) (by omega) (by bv_omega) (by left; bv_omega),
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 pointer (r (.GPR 24#5) s) (by omega)]
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 (pointer + 8#64)
      (r (.GPR 23#5) s) (by bv_omega)]

/-- The large-count edge executes all allocator guards and either the complete
scratch-error RET or the actual Option discriminant load/branch. The successful
checkpoint observes the two freshly stored words even when the limit is None. -/
theorem large_reservation_phase (s u : ArmState) (base : BitVec 64)
    (limit : Option Nat) (data : Ssz.Bytes)
    (owned : Owned s limit data) (counted : Counted s u base limit data)
    (entryCode : CodeAt s base) (nonempty : 0 < data.size)
    (delimiter : data[data.size - 1]! ≠ 0)
    (large : (SszNative.Delimited.countWords data.size
      (Ssz.highestBit data[data.size - 1]!)).high ≠ 0#64) :
    (∃ fuel t, run fuel u = t ∧ Post s t limit data) ∨
      ∃ fuel t ready, run fuel u = t ∧ Ready s t base limit data ready ∧
        r (.GPR 1#5) t = r (.GPR 1#5) s ∧
        read_pc t = if limit.isSome then base + 364#64 else base + 540#64 := by
  let words := SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)
  have wordsLarge : words.high ≠ 0#64 := large
  let address := read_mem_bytes 8 (r (.GPR 4#5) s) s
  let capacity := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
  let used := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by
    have length := owned.length
    bv_omega
  have stack : 112 ≤ (r (.GPR 31#5) s).toNat := by
    simpa only [activationSpan, nonzero, ↓reduceIte] using owned.stackBound
  have spNat : (r (.GPR 31#5) u).toNat = (r (.GPR 31#5) s).toNat - 96 := by
    have savedSp := counted.saved.sp
    bv_omega
  have arg4 := counted.arguments 4#5 (by simp)
  have cursorNat : (r (.GPR 4#5) u + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by
    rw [arg4]
    have bound := owned.arenaBound
    bv_omega
  have header (offset : Nat) (within : offset + 8 ≤ 24) :
      read_mem_bytes 8 (r (.GPR 4#5) u + BitVec.ofNat 64 offset) u =
        read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) s := by
    rw [arg4]
    have bound := owned.arenaBound
    have addrNat : (r (.GPR 4#5) s + BitVec.ofNat 64 offset).toNat =
        (r (.GPR 4#5) s).toNat + offset := by bv_omega
    apply counted.frame.read
    · rw [addrNat]; omega
    · rw [addrNat]
      exact owned.arenaLocal.subspan offset 8 within
  have headerBase : read_mem_bytes 8 (r (.GPR 4#5) u) u = address := by
    simpa only [BitVec.add_zero] using header 0 (by decide)
  have headerCapacity : read_mem_bytes 8 (r (.GPR 4#5) u + 8#64) u = capacity :=
    header 8 (by decide)
  have headerUsed : read_mem_bytes 8 (r (.GPR 4#5) u + 16#64) u = used :=
    header 16 (by decide)
  have range : 2^64 ≤ words.value ∧ words.value < 2^67 := by
    have notSmall : ¬ words.value < 2^64 := fun small =>
      large ((SszNative.Delimited.CountWords.high_zero_iff words).2 small)
    have value := SszNative.Delimited.countWords_value data.size
      (Ssz.highestBit data[data.size - 1]!) owned.physical (SszNative.BitView.highestBit_lt _)
    have physical := owned.physical
    have bit := SszNative.BitView.highestBit_lt data[data.size - 1]!
    change words.value = _ at value
    omega
  have allocated (reservation : SszNative.Arena.Reservation)
      (success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation) :
      SszNative.Delimited.allocation data (arenaOf s) = some reservation := by
    let ready : SszNative.Delimited.Prepared := ⟨words, reservation.used, some reservation⟩
    apply prepared_allocation limit data (arenaOf s) ready owned.physical nonempty delimiter
    have reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
        (arenaOf s).used 2 = some reservation := success
    change SszNative.Delimited.prepare (arenaOf s) words = some ready
    simp only [SszNative.Delimited.prepare, wordsLarge, ↓reduceIte, reserved]
    rfl
  have reservationOwned (reservation : SszNative.Arena.Reservation)
      (success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation) :
      ArenaReservationOwned u reservation := by
    have modelSuccess : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
        (arenaOf s).used 2 = some reservation := success
    obtain ⟨positive, _, _, _, _, physical⟩ := SszNative.Delimited.reservation_bounds
      _ _ _ owned.arenaStorage owned.arenaNonnull reservation modelSuccess
    have separate := (owned.fresh reservation (allocated reservation success)).resolve_left (by decide)
    have apart := separate ((r (.GPR 4#5) s).toNat, 24) (by simp)
    refine ⟨?_, positive, physical, ?_⟩
    · rw [cursorNat]
      have bound := owned.arenaBound
      omega
    · rw [cursorNat]
      omega
  have codeU : CodeAt u base := by simpa only [CodeAt, counted.program] using entryCode
  have pcU : read_pc u = base + 268#64 := by simpa only [large, ↓reduceIte] using counted.pc
  have low : (r (.GPR 24#5) u).toNat = words.value % 2^64 := by
    rw [counted.low]
    exact words.parts.2.1.symm
  have high : (r (.GPR 23#5) u).toNat = words.value / 2^64 := by
    rw [counted.high]
    exact words.parts.2.2.symm
  obtain ⟨fuel, v, reservationRun, reservationFrame, outcome⟩ :=
    arena_reservation_runs u base address capacity used words.value codeU counted.error counted.aligned
      pcU headerBase headerCapacity headerUsed range low high reservationOwned
  have codeV : CodeAt v base := reservationFrame.code base codeU
  have errorV := reservationFrame.error.trans counted.error
  have alignedV := reservationFrame.aligned counted.aligned
  have argsV (reg : BitVec 5) (member : reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5]) :
      r (.GPR reg) v = r (.GPR reg) s := by
    have notChanged : reg ∉ [8#5, 9#5, 10#5, 11#5, 19#5, 20#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reservationFrame.registers reg notChanged).trans (counted.arguments reg member)
  have spV := reservationFrame.sp.trans counted.saved.sp
  rcases outcome with failed | ⟨reservation, success, effect⟩
  · have savedV : Saved s v := counted.saved.of_memory failed.2.2 reservationFrame.sp
      (fun reg _ _ => congrArg (fun word : BitVec 128 => word.setWidth 64) (reservationFrame.vectors reg))
    have tailOwned : TailOwned v := owned.tail_owned nonzero (argsV 0#5 (by simp)) spV
    obtain ⟨t, returnedRun, returned, tailFrame, image⟩ :=
      scratch_correct s v base codeV errorV alignedV failed.2.1 savedV tailOwned
    have before : MemoryFrame (localWrites s) s v := counted.frame.trans
      (fun a _ => congrFun failed.2.2 a)
    have frame : MemoryFrame (localWrites s) s t := before.trans
      (tail_frame_local owned nonzero (argsV 0#5 (by simp)) spV tailFrame)
    have prepareNone : SszNative.Delimited.prepare (arenaOf s) words = none := by
      have reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
          (arenaOf s).used 2 = none := failed.1
      simp only [SszNative.Delimited.prepare, wordsLarge, ↓reduceIte, reserved]
    have model := SszNative.Delimited.run_valid limit data (arenaOf s) nonempty delimiter
    change SszNative.Delimited.run limit data (arenaOf s) =
      (match SszNative.Delimited.prepare (arenaOf s) words with
        | none => ⟨.error .scratchExhausted, (arenaOf s).used, none⟩
        | some ready => SszNative.Delimited.finish limit data.size
            (Ssz.highestBit data[data.size - 1]!) ready) at model
    rw [prepareNone] at model
    left
    refine ⟨fuel + 65, t, ?_, ?_⟩
    · rw [run_plus, reservationRun, returnedRun]
    · apply post_of_frame s t limit data owned returned
      · simpa only [model, SszNative.Delimited.ResultAt, SszNative.UintCodec.scratchExhaustedAt,
          argsV 0#5 (by simp)] using image
      · simp [model, SszNative.Delimited.Outcome.PreparedAt]
      · rw [model]
        have cursor := frame.load ((r (.GPR 4#5) s).toNat + 16) 8
          (by have bound := owned.arenaBound; omega) (owned.arenaLocal.subspan 16 8 (by decide))
        have observed := Option.some.inj cursor
        simpa [arenaOf, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using observed
      · simpa [model, SszNative.Delimited.Outcome.allocation, writesFor] using frame
  · have allocation := allocated reservation success
    have modelSuccess : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
        (arenaOf s).used 2 = some reservation := success
    obtain ⟨positive, pointerAligned, lower, ending, fits, physical⟩ :=
      SszNative.Delimited.reservation_bounds _ _ _ owned.arenaStorage owned.arenaNonnull reservation modelSuccess
    have pointerBound : reservation.pointer < 2^64 := by omega
    have usedBound : reservation.used < 2^64 := by
      have capBound := capacity.isLt
      change reservation.used ≤ capacity.toNat at fits
      omega
    have freshSeparate := (owned.fresh reservation allocation).resolve_left (by decide)
    have freshActivation := freshSeparate (activationSpan s) (by simp [localWrites])
    have arenaSeparate := owned.arenaLocal.resolve_left (by decide)
    have headerActivation := arenaSeparate (activationSpan s) (by simp [localWrites])
    simp only [activationSpan, nonzero, ↓reduceIte] at freshActivation headerActivation
    have savedProtected : Protected (arenaReservationWrites u reservation) (r (.GPR 31#5) u).toNat 96 := by
      right
      intro span member
      simp only [arenaReservationWrites, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [cursorNat, spNat]
        omega
      · simp only [spNat]
        omega
    have savedV : Saved s v := counted.saved.frame effect.frame reservationFrame.sp
      (by rw [spNat]; have bound := (r (.GPR 31#5) s).isLt; omega) savedProtected
      (fun reg _ _ => congrArg (fun word : BitVec 128 => word.setWidth 64) (reservationFrame.vectors reg))
    have reserveFrame : MemoryFrame (writesFor s (some reservation)) u v := by
      apply effect.frame.weaken
      intro span member
      simp only [arenaReservationWrites, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [writesFor, allocatedWrites, cursorNat]
    have frameV : MemoryFrame (writesFor s (some reservation)) s v :=
      (local_frame (some reservation) counted.frame).trans reserveFrame
    have inputsV := inputs_preserved owned (by simpa only [allocation] using frameV)
    let ready : SszNative.Delimited.Prepared := ⟨words, reservation.used, some reservation⟩
    have prepared : SszNative.Delimited.prepare (arenaOf s) words = some ready := by
      simp only [SszNative.Delimited.prepare, wordsLarge, ↓reduceIte, modelSuccess]
      rfl
    have storedV : SszNative.Delimited.PreparedAt (widthLoad v) ready := by
      have stored := reservation_stored_words u v reservation physical effect.memory
      simpa only [SszNative.Delimited.PreparedAt, ready, counted.low, counted.high] using stored
    let t := block base largeLimitOps v
    have dispatch := large_limit_run v base codeV errorV alignedV effect.pc
    have fields := large_limit_fields v base
    have savedT : Saved s t := savedV.of_memory fields.1 fields.2.1
      (fun reg _ _ => congrArg (fun word : BitVec 128 => word.setWidth 64)
        (reserve_limit_vectors v base reg))
    have memoryT := Memory.mem_eq_iff_read_mem_bytes_eq.mp fields.1
    have loadT : widthLoad t = widthLoad v := by
      funext address bytes
      unfold widthLoad
      rw [memoryT]
    have finalPc : read_pc t = if limit.isSome then base + 364#64 else base + 540#64 := by
      have pc := fields.2.2
      rw [argsV 1#5 (by simp), option_tag v (r (.GPR 1#5) s) limit inputsV.option] at pc
      cases limit <;> simpa using pc
    have ptr : r (.GPR 20#5) v = BitVec.ofNat 64 reservation.pointer := by
      rw [← effect.pointer, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    right
    refine ⟨fuel + 3, t, ready, ?_, ?_,
      (reserve_limit_register v base 1#5 (by decide)).trans (argsV 1#5 (by simp)), finalPc⟩
    · rw [run_plus, reservationRun, dispatch]
    · refine ⟨prepared, allocation, (block_program base largeLimitOps v).trans
        (reservationFrame.program.trans counted.program), (block_error base largeLimitOps v).trans errorV,
        block_aligned base largeLimitOps v alignedV, savedT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro reg member
        have notChanged : reg ≠ 8#5 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> decide
        exact (reserve_limit_register v base reg notChanged).trans (argsV reg (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> simp))
      · exact (reserve_limit_register v base 25#5 (by decide)).trans
          ((reservationFrame.registers 25#5 (by decide)).trans counted.preceding)
      · exact (reserve_limit_register v base 26#5 (by decide)).trans
          ((reservationFrame.registers 26#5 (by decide)).trans counted.counter)
      · exact (reserve_limit_register v base 24#5 (by decide)).trans
          ((reservationFrame.registers 24#5 (by decide)).trans counted.low)
      · exact (reserve_limit_register v base 23#5 (by decide)).trans
          ((reservationFrame.registers 23#5 (by decide)).trans counted.high)
      · exact (reserve_limit_register v base 20#5 (by decide)).trans ptr
      · exact (reserve_limit_register v base 19#5 (by decide)).trans effect.words
      · rw [loadT]
        exact storedV
      · have cursor := effect.cursor
        rw [arg4] at cursor
        rw [memoryT, cursor]
        exact Nat.mod_eq_of_lt usedBound
      · exact frameV.trans (fun a _ => congrFun fields.1 a)

end SszArm.Delimited
