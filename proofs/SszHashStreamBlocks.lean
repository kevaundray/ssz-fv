import Ssz.Hash.Sha256

namespace SszNative.HashStream

/-- The pinned SHA compression primitive applied to a semantic byte block. -/
def compressList (s : Vector UInt32 8) (xs : List UInt8) : Vector UInt32 8 :=
  Ssz.Sha256.compress s ⟨xs.toArray⟩ 0

private theorem schedulePrefix_locality (a b : ByteArray) (start other : Nat)
    (agree : ∀ i, i < 64 → a.get! (start + i) = b.get! (other + i))
    (count : Nat) :
    Ssz.Sha256.schedulePrefix a start count =
      Ssz.Sha256.schedulePrefix b other count := by
  have words (i : Nat) (hi : i + 4 ≤ 64) :
      Ssz.Sha256.wordAt a (start + i) = Ssz.Sha256.wordAt b (other + i) := by
    simp only [Ssz.Sha256.wordAt, Nat.add_assoc]
    rw [agree i (by omega), agree (i + 1) (by omega),
      agree (i + 2) (by omega), agree (i + 3) (by omega)]
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [Ssz.Sha256.schedulePrefix, ih]
    split
    · rename_i first
      rw [words (4 * count) (by omega)]
    · rfl

/-- Compression reads only the sixty-four bytes at its source offset.
Both source intervals are in bounds; no out-of-bounds fallback is used. -/
theorem compress_locality (s : Vector UInt32 8) (a b : ByteArray)
    (start other : Nat) (ha : start + 64 ≤ a.size) (hb : other + 64 ≤ b.size)
    (agree : ∀ i (hi : i < 64),
      a[start + i]'(by omega) = b[other + i]'(by omega)) :
    Ssz.Sha256.compress s a start = Ssz.Sha256.compress s b other := by
  have bytes (i : Nat) (hi : i < 64) :
      a.get! (start + i) = b.get! (other + i) := by
    change a.data[start + i]! = b.data[other + i]!
    rw [getElem!_pos a.data (start + i) (by simpa using (show start + i < a.size by omega)),
      getElem!_pos b.data (other + i) (by simpa using (show other + i < b.size by omega))]
    exact agree i hi
  have schedules : Ssz.Sha256.schedule a start = Ssz.Sha256.schedule b other :=
    schedulePrefix_locality a b start other bytes 64
  simp only [Ssz.Sha256.compress, schedules]

/-- Direct compression of an original allocation is the semantic compression
of exactly its next sixty-four bytes, without changing the native access path. -/
theorem compress_eq_compressList (s : Vector UInt32 8) (input : ByteArray)
    (start : Nat) (bound : start + 64 ≤ input.size) :
    Ssz.Sha256.compress s input start =
      compressList s ((input.data.toList.drop start).take 64) := by
  unfold compressList
  refine compress_locality s input ⟨((input.data.toList.drop start).take 64).toArray⟩
    start 0 bound ?_ ?_
  · change 0 + 64 ≤ ((input.data.toList.drop start).take 64).toArray.size
    simp only [List.size_toArray, List.length_take, List.length_drop,
      Array.length_toList, ByteArray.size_data]
    omega
  · intro i hi
    simp only [ByteArray.getElem_eq_getElem_data, Nat.zero_add,
      List.getElem_toArray, List.getElem_take, List.getElem_drop, Array.getElem_toList] <;> rfl

/-- Canonical left-to-right absorption of all complete blocks. The second
component is the uncompressed byte suffix, not a padded block. -/
def absorb (s : Vector UInt32 8) (xs : List UInt8) : Vector UInt32 8 × List UInt8 :=
  if _ : 64 ≤ xs.length then
    absorb (compressList s (xs.take 64)) (xs.drop 64)
  else
    (s, xs)
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-- A short byte stream does not invoke compression. -/
theorem absorb_short (s : Vector UInt32 8) (xs : List UInt8) (h : xs.length < 64) :
    absorb s xs = (s, xs) := by
  rw [absorb]
  simp only [show ¬64 ≤ xs.length by omega, ↓reduceDIte]

/-- One complete block can be split off the semantic stream. -/
theorem absorb_step (s : Vector UInt32 8) (xs : List UInt8) (h : 64 ≤ xs.length) :
    absorb s xs = absorb (compressList s (xs.take 64)) (xs.drop 64) := by
  rw [absorb]
  simp only [h, ↓reduceDIte]

@[simp] theorem absorb_nil (s : Vector UInt32 8) : absorb s [] = (s, []) :=
  absorb_short s [] (by simp)

/-- The residual invariant is unconditional, including for an arbitrary
initial chaining state. -/
theorem absorb_residual_lt (s : Vector UInt32 8) (xs : List UInt8) :
    (absorb s xs).2.length < 64 := by
  by_cases h : 64 ≤ xs.length
  · rw [absorb_step s xs h]
    exact absorb_residual_lt (compressList s (xs.take 64)) (xs.drop 64)
  · rw [absorb_short s xs (by omega)]
    exact Nat.lt_of_not_ge h
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-- The semantic residue is exactly the suffix after the whole-block prefix. -/
theorem absorb_residual_eq_drop (s : Vector UInt32 8) (xs : List UInt8) :
    (absorb s xs).2 = xs.drop (64 * (xs.length / 64)) := by
  by_cases h : 64 ≤ xs.length
  · rw [absorb_step s xs h, absorb_residual_eq_drop]
    simp only [List.length_drop, List.drop_drop]
    congr 1
    omega
  · rw [absorb_short s xs (by omega)]
    simp only [show xs.length / 64 = 0 by omega, Nat.mul_zero, List.drop_zero]
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-- The buffer occupancy is the byte count modulo the compression width. -/
theorem absorb_residual_length (s : Vector UInt32 8) (xs : List UInt8) :
    (absorb s xs).2.length = xs.length % 64 := by
  rw [absorb_residual_eq_drop, List.length_drop]
  omega

/-- Updating a completed-block state with its residual and a new suffix is
identical to absorbing the concatenation. -/
theorem absorb_append (s : Vector UInt32 8) (xs ys : List UInt8) :
    absorb s (xs ++ ys) = absorb (absorb s xs).1 ((absorb s xs).2 ++ ys) := by
  by_cases h : 64 ≤ xs.length
  · rw [absorb_step s (xs ++ ys) (by simp only [List.length_append]; omega),
      List.take_append_of_le_length h, List.drop_append_of_le_length h,
      absorb_step s xs h]
    exact absorb_append (compressList s (xs.take 64)) (xs.drop 64) ys
  · rw [absorb_short s xs (by omega)]
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-- A complete prefix leaves no buffered bytes for its successor. -/
theorem absorb_append_aligned (s : Vector UInt32 8) (xs ys : List UInt8)
    (aligned : xs.length % 64 = 0) :
    absorb s (xs ++ ys) = absorb (absorb s xs).1 ys := by
  rw [absorb_append, absorb_residual_eq_drop]
  have full : 64 * (xs.length / 64) = xs.length := by omega
  simp only [full, List.drop_length, List.nil_append]

/-- An exact block performs exactly one compression and leaves no residue. -/
theorem absorb_block (s : Vector UInt32 8) (xs : List UInt8) (size : xs.length = 64) :
    absorb s xs = (compressList s xs, []) := by
  rw [absorb_step s xs (by omega), List.take_of_length_le (by omega),
    List.drop_eq_nil_of_le (by omega), absorb_nil]

/-- Useful when a native buffered prefix and a copied suffix fill one block. -/
theorem absorb_block_append (s : Vector UInt32 8) (xs ys : List UInt8)
    (size : xs.length = 64) :
    absorb s (xs ++ ys) = absorb (compressList s xs) ys := by
  rw [absorb_append, absorb_block s xs size]
  rfl

/-- Splitting an arbitrary stream at any byte boundary preserves absorption. -/
theorem absorb_split (s : Vector UInt32 8) (xs : List UInt8) (cut : Nat) :
    absorb s xs = absorb (absorb s (xs.take cut)).1
      ((absorb s (xs.take cut)).2 ++ xs.drop cut) := by
  simpa only [List.take_append_drop] using
    absorb_append s (xs.take cut) (xs.drop cut)

/-- An in-place native direct-block loop can consume any bounded number of
blocks. Its offsets retain the original input allocation. -/
theorem absorb_rangeFold_split (count : Nat) (s : Vector UInt32 8)
    (input : ByteArray) (start : Nat) (bound : start + 64 * count ≤ input.size) :
    absorb s (input.data.toList.drop start) =
      absorb ((List.range count).foldl
        (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) s)
        (input.data.toList.drop (start + 64 * count)) := by
  induction count generalizing s start with
  | zero => simp
  | succ count ih =>
    have first : start + 64 ≤ input.size := by omega
    have enough : 64 ≤ (input.data.toList.drop start).length := by
      simp only [List.length_drop, Array.length_toList, ByteArray.size_data]
      omega
    rw [absorb_step s (input.data.toList.drop start) enough,
      ← compress_eq_compressList s input start first, List.drop_drop]
    rw [ih (Ssz.Sha256.compress s input start) (start + 64) (by omega)]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
      Nat.mul_zero, Nat.add_zero]
    have offsets :
        (fun current i => Ssz.Sha256.compress current input (start + 64 + 64 * i)) =
        (fun current i => Ssz.Sha256.compress current input (start + 64 * Nat.succ i)) := by
      funext current i
      congr 1
      omega
    rw [offsets]
    have endOffset : start + 64 + 64 * count = start + 64 * Nat.succ count := by omega
    rw [endOffset]

/-- Canonical completed-block absorption equals the native/reference indexed
fold, including when the direct loop begins after a buffered-prefix copy. -/
theorem absorb_drop_eq_rangeFold (s : Vector UInt32 8) (input : ByteArray)
    (start : Nat) (bound : start ≤ input.size) :
    (absorb s (input.data.toList.drop start)).1 =
      (List.range ((input.size - start) / 64)).foldl
        (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) s := by
  rw [absorb_rangeFold_split ((input.size - start) / 64) s input start (by omega)]
  rw [absorb_short]
  · simp only [List.length_drop, Array.length_toList, ByteArray.size_data]
    omega

/-- The pinned SHA whole-allocation block fold and canonical semantic
completed-block absorption agree, for arbitrary byte lengths. -/
theorem absorb_eq_rangeFold (s : Vector UInt32 8) (input : ByteArray) :
    (absorb s input.data.toList).1 =
      (List.range (input.size / 64)).foldl
        (fun current i => Ssz.Sha256.compress current input (64 * i)) s := by
  simpa only [List.drop_zero, Nat.sub_zero, Nat.zero_add] using
    absorb_drop_eq_rangeFold s input 0 (Nat.zero_le _)

/-- Reference hashing is digest emission after canonical absorption of the
actual pinned padded bytes, not an oracle for a future native result. -/
theorem hash_eq_absorb_pad (input : ByteArray) :
    Ssz.Sha256.hash input = Ssz.Sha256.digest
      (absorb Ssz.Sha256.initialState (Ssz.Sha256.pad input).data.toList).1 := by
  rw [absorb_eq_rangeFold]
  rfl

end SszNative.HashStream
