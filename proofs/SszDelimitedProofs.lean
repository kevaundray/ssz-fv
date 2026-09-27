import SszDelimited

set_option autoImplicit false

namespace SszNative.Delimited

/-- Word construction is exact for every physically representable byte count. -/
theorem countWords_value (length highest : Nat) (physical : length < 2^64)
    (bit : highest < 8) :
    (countWords length highest).value = 8 * (length - 1) + highest := by
  have preceding : length - 1 < 2^64 := by omega
  have low : (countWords length highest).low.toNat =
      (8 * (length - 1) + highest) % 2^64 := by
    simp only [countWords, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have high : (countWords length highest).high.toNat = (length - 1) / 2^61 := by
    simp only [countWords, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt preceding, Nat.shiftRight_eq_div_pow]
  have quotient : (8 * (length - 1) + highest) / 2^64 = (length - 1) / 2^61 := by
    omega
  simp only [CountWords.value, low, high, ← quotient]
  omega

theorem CountWords.high_zero_iff (count : CountWords) :
    count.high = 0#64 ↔ count.value < 2^64 := by
  have low := count.low.isLt
  have high := count.high.isLt
  have zero : count.high = 0#64 ↔ count.high.toNat = 0 := by
    rw [← BitVec.toNat_inj]
    rfl
  rw [zero]
  unfold CountWords.value
  omega

theorem countWords_data_value (data : Ssz.Bytes) (physical : data.size < 2^64) :
    (countWords data.size (Ssz.highestBit data[data.size - 1]!)).value =
      BitView.delimitedCount data :=
  countWords_value data.size _ physical (BitView.highestBit_lt _)

theorem prepare_none_iff (arena : ArenaState) (count : CountWords) :
    prepare arena count = none ↔ count.high ≠ 0#64 ∧
      Arena.reserve arena.base arena.capacity arena.used 2 = none := by
  by_cases zero : count.high = 0#64
  · simp [prepare, zero]
  · cases reservation : Arena.reserve arena.base arena.capacity arena.used 2 <;>
      simp [prepare, zero, reservation]

theorem prepare_count (arena : ArenaState) (count : CountWords) (ready : Prepared)
    (prepared : prepare arena count = some ready) : ready.count = count := by
  by_cases zero : count.high = 0#64
  · simp [prepare, zero] at prepared
    cases prepared
    rfl
  · cases reservation : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none => simp [prepare, zero, reservation] at prepared
    | some region =>
      simp [prepare, zero, reservation] at prepared
      cases prepared
      rfl

theorem prepare_cursor (arena : ArenaState) (count : CountWords) (ready : Prepared)
    (prepared : prepare arena count = some ready) :
    ready.used = match ready.allocation with
      | none => arena.used
      | some reservation => reservation.used := by
  by_cases zero : count.high = 0#64
  · simp [prepare, zero] at prepared
    cases prepared
    rfl
  · cases reservation : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none => simp [prepare, zero, reservation] at prepared
    | some region =>
      simp [prepare, zero, reservation] at prepared
      cases prepared
      rfl

/-- A complete interface for the post-validation phase; no register state leaks. -/
theorem run_valid (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0) :
    run limit data arena =
      match prepare arena (countWords data.size (Ssz.highestBit data[data.size - 1]!)) with
      | none => ⟨.error .scratchExhausted, arena.used, none⟩
      | some ready => finish limit data.size (Ssz.highestBit data[data.size - 1]!) ready := by
  have nonzero : data.size ≠ 0 := by omega
  simp [run, validate, nonzero, delimiter]
  rfl

theorem finish_resource (limit : Option Nat) (length highest : Nat) (ready : Prepared) :
    (finish limit length highest ready).used = ready.used ∧
    (finish limit length highest ready).prepared = some ready := by
  exact ⟨rfl, rfl⟩

/-- Materializing the returned view recovers the logical SSZ bits. -/
theorem finish_erase (limit : Option Nat) (data : Ssz.Bytes) (ready : Prepared)
    (nonempty : 0 < data.size) (value : ready.count.value = BitView.delimitedCount data) :
    (finish limit data.size (Ssz.highestBit data[data.size - 1]!) ready).erase data =
      some (match limit with
        | none => .ok (.bits (Ssz.unpackBits data (BitView.delimitedCount data)))
        | some cap => if BitView.delimitedCount data ≤ cap then
            .ok (.bits (Ssz.unpackBits data (BitView.delimitedCount data)))
          else .error (.overLimit cap (BitView.delimitedCount data))) := by
  have keep : retainedBytes data.size (Ssz.highestBit data[data.size - 1]!) =
      (BitView.delimitedCount data + 7) / 8 :=
    (BitView.delimited_byte_count data nonempty).symm
  have bits : Ssz.unpackBits
      (data.extract 0 (retainedBytes data.size (Ssz.highestBit data[data.size - 1]!)))
      ready.count.value = Ssz.unpackBits data (BitView.delimitedCount data) := by
    rw [value, keep]
    exact BitView.delimited_unpack_retained data nonempty
  cases limit with
  | none => simp [finish, Outcome.erase, bits]
  | some cap =>
    rw [value] at bits
    by_cases bounded : BitView.delimitedCount data ≤ cap
    · simp [finish, Outcome.erase, value, bounded, bits]
    · simp [finish, Outcome.erase, value, bounded]

/-- Exact semantic correspondence, including the precisely characterized host
failure. This is stronger than conditional correctness of successful results. -/
theorem run_refines (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) :
    (run limit data arena).erase data =
      if Exhausted data arena then none else some (BitView.delimitedOutcome limit data) := by
  by_cases empty : data.size = 0
  · simp [run, validate, empty, Outcome.erase, Exhausted, NeedsAllocation,
      BitView.delimitedOutcome]
  · have nonempty : 0 < data.size := by omega
    by_cases finalZero : data[data.size - 1]! = 0
    · by_cases allZero : data.all (· == 0) = true <;>
        simp [run, validate, empty, finalZero, scanZeros, allZero, Outcome.erase,
          Exhausted, NeedsAllocation, BitView.delimitedOutcome]
    · have value := countWords_data_value data physical
      by_cases small : (countWords data.size (Ssz.highestBit data[data.size - 1]!)).high = 0#64
      · have below : BitView.delimitedCount data < 2^64 := by
          rw [← value]
          exact CountWords.high_zero_iff _ |>.mp small
        have noAllocation : ¬ NeedsAllocation data := by
          simp [NeedsAllocation, empty, finalZero, Nat.not_le.mpr below]
        rw [run_valid limit data arena nonempty finalZero]
        simp only [prepare, small, ↓reduceIte]
        rw [finish_erase limit data _ nonempty value]
        simp [Exhausted, noAllocation, BitView.delimitedOutcome, empty, finalZero]
        rfl
      · have large : 2^64 ≤ BitView.delimitedCount data := by
          have below : ¬ (countWords data.size
              (Ssz.highestBit data[data.size - 1]!)).value < 2^64 :=
            fun h => small ((CountWords.high_zero_iff _).mpr h)
          rw [value] at below
          omega
        have needs : NeedsAllocation data := by
          simp [NeedsAllocation, empty, finalZero, large]
        cases reservation : Arena.reserve arena.base arena.capacity arena.used 2 with
        | none =>
          simp [run, validate, empty, finalZero, prepare, small, reservation,
            Outcome.erase, Exhausted, needs]
        | some region =>
          rw [run_valid limit data arena nonempty finalZero]
          simp only [prepare, small, ↓reduceIte, reservation]
          rw [finish_erase limit data _ nonempty value]
          simp [Exhausted, reservation, BitView.delimitedOutcome, empty, finalZero]
          rfl

theorem run_bitList (limit : Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) :
    (run (some limit) data arena).erase data =
      if Exhausted data arena then none else some (Ssz.deserialize (.bitList limit) data) := by
  rw [run_refines _ _ _ physical, BitView.list_outcome_eq_deserialize]

theorem run_progressiveBitList (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) :
    (run limit data arena).erase data =
      if Exhausted data arena then none else some (Ssz.deserialize (.progressiveBitList limit) data) := by
  rw [run_refines _ _ _ physical, BitView.progressive_outcome_eq_deserialize]

theorem Outcome.erase_none_iff (outcome : Outcome) (data : Ssz.Bytes) :
    outcome.erase data = none ↔ outcome.result = .error .scratchExhausted := by
  cases result : outcome.result with
  | ok view => simp [Outcome.erase, result]
  | error reason => cases reason <;> simp [Outcome.erase, result]

theorem run_scratch_iff (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) :
    (run limit data arena).result = .error .scratchExhausted ↔ Exhausted data arena := by
  rw [← Outcome.erase_none_iff (run limit data arena) data, run_refines _ _ _ physical]
  by_cases exhausted : Exhausted data arena <;> simp [exhausted]

/-- Reservation and cursor effects do not depend on the optional limit. In
particular, over-limit rejection does not roll back a successful reservation. -/
theorem run_resources (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) :
    (run limit data arena).allocation = allocation data arena ∧
    (run limit data arena).used =
      match allocation data arena with
      | none => arena.used
      | some reservation => reservation.used := by
  by_cases empty : data.size = 0
  · simp [run, validate, empty, Outcome.allocation, allocation, NeedsAllocation]
  · by_cases finalZero : data[data.size - 1]! = 0
    · cases zeros : scanZeros data <;>
        simp [run, validate, empty, finalZero, zeros, Outcome.allocation,
          allocation, NeedsAllocation]
    · have value := countWords_data_value data physical
      have needs : NeedsAllocation data ↔
          (countWords data.size (Ssz.highestBit data[data.size - 1]!)).high ≠ 0#64 := by
        simp only [NeedsAllocation, empty, finalZero, ↓reduceIte, ne_eq,
          CountWords.high_zero_iff, value, Nat.not_lt]
      by_cases small : (countWords data.size (Ssz.highestBit data[data.size - 1]!)).high = 0#64
      · have noAllocation : ¬ NeedsAllocation data := fun h => needs.mp h small
        simp [run, validate, empty, finalZero, prepare, small, finish,
          Outcome.allocation, allocation, noAllocation]
      · have allocationNeeded := needs.mpr small
        cases reservation : Arena.reserve arena.base arena.capacity arena.used 2 <;>
          simp [run, validate, empty, finalZero, prepare, small, reservation,
            finish, Outcome.allocation, allocation, allocationNeeded]

/-- Physical two-word reservation geometry, without a signed capacity bound. -/
theorem reservation_bounds (address capacity used : Nat)
    (storage : address + capacity ≤ 2^64)
    (nonnull : 0 < capacity → 0 < address)
    (r : Arena.Reservation) (reserved : Arena.reserve address capacity used 2 = some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
    address + used ≤ r.pointer ∧ r.pointer + 16 = address + r.used ∧
    r.used ≤ capacity ∧ r.pointer + 16 ≤ 2^64 := by
  obtain ⟨checks, rfl⟩ :=
    (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  have start := Arena.used_le_start address used
  have aligned := Arena.aligned_mod (address + used)
  have point := Arena.start_pointer address used
  have fits := checks.2.2.2.2.2
  have positive : 0 < capacity := by
    dsimp only [Arena.finish] at fits
    omega
  have basepos := nonnull positive
  dsimp only
  refine ⟨by omega, ?_, by omega, ?_, fits, ?_⟩
  · simpa only [point] using aligned
  · simp only [Arena.finish, Nat.reduceMul, Nat.add_assoc]
  · dsimp only [Arena.finish] at fits
    omega

theorem validate_ok_iff (data : Ssz.Bytes) (byte : UInt8) :
    validate data = .ok byte ↔
      0 < data.size ∧ data[data.size - 1]! ≠ 0 ∧ byte = data[data.size - 1]! := by
  by_cases empty : data.size = 0
  · simp [validate, empty]
  · have nonempty : 0 < data.size := by omega
    by_cases zero : data[data.size - 1]! = 0
    · cases zeros : scanZeros data <;> simp [validate, empty, zero, zeros]
    · simp [validate, empty, zero, nonempty, eq_comm]

theorem finish_success (limit : Option Nat) (length highest : Nat) (ready : Prepared)
    (view : Borrowed) (success : (finish limit length highest ready).result = .ok view) :
    view = ⟨0, retainedBytes length highest, ready.count⟩ := by
  cases limit with
  | none => simpa [finish] using success.symm
  | some cap =>
    by_cases bounded : ready.count.value ≤ cap
    · simpa [finish, bounded] using success.symm
    · simp [finish, bounded] at success

theorem run_success_shape (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) (view : Borrowed)
    (success : (run limit data arena).result = .ok view) :
    view.offset = 0 ∧ view.bytes = (view.count.value + 7) / 8 ∧ view.bytes ≤ data.size := by
  cases validation : validate data with
  | error reason => simp [run, validation] at success
  | ok byte =>
    obtain ⟨nonempty, _, rfl⟩ := (validate_ok_iff data byte).mp validation
    cases prepared : prepare arena (countWords data.size (Ssz.highestBit data[data.size - 1]!)) with
    | none => simp [run, validation, prepared] at success
    | some ready =>
      have finished : (finish limit data.size (Ssz.highestBit data[data.size - 1]!) ready).result =
          .ok view := by simpa only [run, validation, prepared] using success
      have shape := finish_success limit data.size _ ready view finished
      subst view
      have count := prepare_count arena _ ready prepared
      have value : ready.count.value = BitView.delimitedCount data := by
        rw [count]
        exact countWords_data_value data physical
      refine ⟨rfl, ?_, ?_⟩
      · simpa only [value, retainedBytes] using (BitView.delimited_byte_count data nonempty).symm
      · simp only [retainedBytes]
        split <;> omega

theorem CountWords.parts (count : CountWords) :
    count.value < 2^128 ∧ count.value % 2^64 = count.low.toNat ∧
      count.value / 2^64 = count.high.toNat := by
  have low := count.low.isLt
  have high := count.high.isLt
  unfold CountWords.value
  omega

theorem borrowed_result_refines (observe : Nat → Nat → Option Nat)
    (out source optionAddress : Nat) (data : Ssz.Bytes) (outcome : Outcome) (view : Borrowed)
    (result : outcome.result = .ok view)
    (observed : ResultAt observe out source optionAddress data outcome)
    (offset : view.offset = 0) (bytes : view.bytes = (view.count.value + 7) / 8)
    (within : view.bytes ≤ data.size) :
    BitView.ResultAt observe out (.ok (.bits
      (Ssz.unpackBits (data.extract view.offset (view.offset + view.bytes)) view.count.value))) := by
  simp only [ResultAt, result] at observed
  obtain ⟨tag, kind, pointer, length, low, high, memory⟩ := observed
  have packedSize : (data.extract 0 view.bytes).size = view.bytes := by
    simp [Array.size_extract, Nat.min_eq_left within]
  have packedMemory : ByteView.BytesAt observe source (data.extract 0 view.bytes) := by
    intro i inside
    have sourceInside : i < data.size := by rw [packedSize] at inside; omega
    have original := memory i sourceInside
    simpa only [Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem sourceInside,
      Option.getD_some, Array.getElem_extract, Nat.zero_add] using original
  obtain ⟨bound, lowValue, highValue⟩ := view.count.parts
  simp only [offset, Nat.zero_add, BitView.ResultAt, Packing.unpackBits_size]
  refine ⟨tag, kind, bound, ?_, ?_, source, data.extract 0 view.bytes, ?_, ?_, ?_,
    packedMemory, rfl⟩
  · simpa only [lowValue] using low
  · simpa only [highValue] using high
  · simpa only [offset, Nat.add_zero] using pointer
  · simpa only [packedSize] using length
  · exact packedSize.trans bytes

/-- ISA clients discharge one shared model observation, then use this theorem
to recover the original SSZ memory relation without duplicating semantic cases. -/
theorem result_refines (observe : Nat → Nat → Option Nat) (out source optionAddress : Nat)
    (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState)
    (physical : data.size < 2^64) (resources : ¬ Exhausted data arena)
    (observed : ResultAt observe out source optionAddress data (run limit data arena)) :
    BitView.ResultAt observe out (BitView.delimitedOutcome limit data) := by
  have erased := run_refines limit data arena physical
  simp only [resources, ↓reduceIte] at erased
  cases result : (run limit data arena).result with
  | ok view =>
    have value := Option.some.inj (by simpa only [Outcome.erase, result] using erased)
    rw [← value]
    obtain ⟨offset, bytes, within⟩ := run_success_shape limit data arena physical view result
    exact borrowed_result_refines observe out source optionAddress data _ view result
      observed offset bytes within
  | error reason =>
    cases reason with
    | scratchExhausted => simp [Outcome.erase, result] at erased
    | semantic reason =>
      have value := Option.some.inj (by simpa only [Outcome.erase, result] using erased)
      rw [← value]
      cases reason <;> simp only [ResultAt, result] at observed <;>
        first | exact observed | exact observed.1

/-- The two actual stored words, with no arena or instruction-state assumption. -/
theorem CountWords.pair_of_words (observe : Nat → Nat → Option Nat)
    (pointer : BitVec 64) (count : CountWords)
    (positive : 0 < pointer.toNat) (aligned : pointer.toNat % 8 = 0)
    (bound : pointer.toNat + 16 ≤ 2^64)
    (low : observe pointer.toNat 8 = some count.low.toNat)
    (high : observe (pointer.toNat + 8) 8 = some count.high.toNat) :
    NatMemory.Pair observe pointer 2#64 count.value := by
  right
  refine ⟨[count.low, count.high], positive, aligned, ?_, rfl, ?_, ?_⟩
  · simpa using bound
  · intro i
    have index : i.val = 0 ∨ i.val = 1 := by
      have bounded : i.val < 2 := i.isLt
      omega
    rcases index with first | second
    · simpa [first] using low
    · simpa [second] using high
  · simp [Limbs.value, CountWords.value]

/-- The prepared count supplies the existing native comparison ABI. All
architecture-specific stores and frame transport stay outside this lemma. -/
theorem PreparedAt.pair (observe : Nat → Nat → Option Nat) (arena : ArenaState)
    (count : CountWords) (ready : Prepared) (prepared : prepare arena count = some ready)
    (stored : PreparedAt observe ready) (storage : arena.base + arena.capacity ≤ 2^64)
    (nonnull : 0 < arena.capacity → 0 < arena.base) :
    NatMemory.Pair observe (BitVec.ofNat 64 ready.pointer) (BitVec.ofNat 64 ready.payload)
      ready.count.value := by
  by_cases zero : count.high = 0#64
  · simp [prepare, zero] at prepared
    cases prepared
    left
    constructor
    · rfl
    · simp [Prepared.payload, CountWords.value, zero]
  · cases reservation : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none => simp [prepare, zero, reservation] at prepared
    | some region =>
      simp [prepare, zero, reservation] at prepared
      cases prepared
      obtain ⟨positive, aligned, _, _, _, bound⟩ :=
        reservation_bounds arena.base arena.capacity arena.used storage nonnull region reservation
      have pointerBound : region.pointer < 2^64 := by omega
      change observe region.pointer 8 = some count.low.toNat ∧
        observe (region.pointer + 8) 8 = some count.high.toNat at stored
      apply CountWords.pair_of_words observe _ count
      · simpa [Prepared.pointer, Nat.mod_eq_of_lt pointerBound] using positive
      · simpa [Prepared.pointer, Nat.mod_eq_of_lt pointerBound] using aligned
      · simpa [Prepared.pointer, Nat.mod_eq_of_lt pointerBound] using bound
      · simpa [Prepared.pointer, Nat.mod_eq_of_lt pointerBound] using stored.1
      · simpa [Prepared.pointer, Nat.mod_eq_of_lt pointerBound] using stored.2

end SszNative.Delimited
