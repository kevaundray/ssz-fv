import SszHashStream
import SszHashStreamBlocks
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Lemmas

set_option autoImplicit false

namespace SszNative.HashStream

/-- The initialized prefix after a bounded interval copy. The untouched tail
is deliberately absent from the semantic byte stream. -/
theorem copy_take (buf : Vector UInt8 64) (dst : Nat) (input : ByteArray)
    (src count : Nat) (hd : dst + count ≤ 64)
    (hs : src + count ≤ input.size) :
    (copy buf dst input src count hd hs).toList.take (dst + count) =
      buf.toList.take dst ++ (input.data.toList.drop src).take count := by
  have hd' : dst ≤ 64 := by omega
  have hl : (buf.toList.take dst).length = dst := by simp [Nat.min_eq_left hd']
  apply List.ext_getElem
  · simp only [List.length_take, Vector.length_toList, List.length_append,
      List.length_drop, Array.length_toList, ByteArray.size_data]
    omega
  · intro i hi hj
    have hib : i < 64 := by
      have := List.length_take_le' (dst + count) (copy buf dst input src count hd hs).toList
      simp only [Vector.length_toList] at this
      omega
    have hic : i < dst + count := by
      simpa [Nat.min_eq_left hd] using hi
    by_cases hid : i < dst
    · rw [List.getElem_append_left (by simpa [hl] using hid)]
      simp only [List.getElem_take, Vector.getElem_toList]
      exact copy_outside buf dst input src count hd hs i hib (by omega)
    · rw [List.getElem_append_right (by simpa [hl] using (show dst ≤ i by omega))]
      simp only [List.getElem_take, List.getElem_drop, Vector.getElem_toList,
        Array.getElem_toList, hl]
      exact copy_inside buf dst input src count hd hs i hib (by omega)

/-- Direct blocks and the final copy have the canonical list semantics. -/
theorem drain_absorb (buf : Vector UInt8 64) (chaining : Vector UInt32 8)
    (byteLen : UInt64) (input : ByteArray) (start : Nat)
    (hs : start ≤ input.size) :
    ((drain buf chaining byteLen input start hs).state.chaining,
      (drain buf chaining byteLen input start hs).state.buffer.toList.take
        (drain buf chaining byteLen input start hs).state.buffered.val) =
      absorb chaining (input.data.toList.drop start) := by
  apply Prod.ext
  · exact (absorb_drop_eq_rangeFold chaining input start hs).symm
  · dsimp only [drain]
    have copied := copy_take buf 0 input (start + 64 * ((input.size - start) / 64))
      ((input.size - start) % 64) (by omega) (by omega)
    simp only [Nat.zero_add, List.take_zero, List.nil_append] at copied
    rw [copied]
    rw [absorb_residual_eq_drop]
    simp only [List.length_drop, Array.length_toList, ByteArray.size_data,
      List.drop_drop]
    have hn := Nat.mod_add_div (input.size - start) 64
    have hlen :
        (input.data.toList.drop (start + 64 * ((input.size - start) / 64))).length =
          (input.size - start) % 64 := by
      simp only [List.length_drop, Array.length_toList, ByteArray.size_data]
      omega
    rw [← hlen, List.take_length]

/-- One native update absorbs exactly the live prefix followed by its input,
even when the state did not originate at the standard SHA initial state. -/
theorem update_absorb (s : State) (input : ByteArray) :
    ((update s input).state.chaining,
      (update s input).state.buffer.toList.take (update s input).state.buffered.val) =
      absorb s.chaining (s.buffer.toList.take s.buffered.val ++ input.data.toList) := by
  have hb := s.buffered.isLt
  have hlen : (s.buffer.toList.take s.buffered.val).length = s.buffered.val := by
    simp [Nat.min_eq_left (Nat.le_of_lt hb)]
  unfold update
  split
  · rename_i empty
    simpa only [empty, List.take_zero, List.nil_append, List.drop_zero] using
      drain_absorb s.buffer s.chaining (s.byteLen + UInt64.ofNat input.size) input 0
        (Nat.zero_le _)
  · rename_i nonempty
    dsimp only
    split
    · rename_i incomplete
      have hc : min (64 - s.buffered.val) input.size = input.size := by omega
      rw [absorb_short s.chaining _ (by
        simp only [List.length_append, hlen, Array.length_toList, ByteArray.size_data]
        omega)]
      apply Prod.ext
      · rfl
      · dsimp only
        rw [copy_take]
        simp only [List.drop_zero, hc]
        rw [List.take_of_length_le (l := input.data.toList) (i := input.size) (by
          simp only [Array.length_toList, ByteArray.size_data, Nat.le_refl])]
    · rename_i complete
      have hc : min (64 - s.buffered.val) input.size = 64 - s.buffered.val := by omega
      have heq : s.buffered.val + min (64 - s.buffered.val) input.size = 64 := by omega
      have enough : 64 ≤ (s.buffer.toList.take s.buffered.val ++ input.data.toList).length := by
        simp only [List.length_append, hlen, Array.length_toList, ByteArray.size_data]
        omega
      rw [absorb_step s.chaining _ enough]
      have htake :
          (s.buffer.toList.take s.buffered.val ++ input.data.toList).take 64 =
            s.buffer.toList.take s.buffered.val ++
              input.data.toList.take (min (64 - s.buffered.val) input.size) := by
        rw [List.take_append, hlen, hc]
        simp [List.take_take, Nat.min_eq_right (Nat.le_of_lt hb)]
      have hdrop :
          (s.buffer.toList.take s.buffered.val ++ input.data.toList).drop 64 =
            input.data.toList.drop (min (64 - s.buffered.val) input.size) := by
        rw [List.drop_append, hlen, hc]
        simp [List.drop_eq_nil_of_le (by omega :
          (s.buffer.toList.take s.buffered.val).length ≤ 64)]
      rw [htake, hdrop]
      rw [drain_absorb]
      have hcopy := copy_take s.buffer s.buffered.val input 0
        (min (64 - s.buffered.val) input.size)
        (by omega) (by have := Nat.min_le_right (64 - s.buffered.val) input.size; omega)
      simp only [heq] at hcopy
      have hbuffer :
          (copy s.buffer s.buffered.val input 0
            (min (64 - s.buffered.val) input.size) (by omega)
            (by have := Nat.min_le_right (64 - s.buffered.val) input.size; omega)).toList =
          s.buffer.toList.take s.buffered.val ++
            input.data.toList.take (min (64 - s.buffered.val) input.size) := by
        simpa only [List.drop_zero,
          List.take_of_length_le (by simp : (copy s.buffer s.buffered.val input 0
            (min (64 - s.buffered.val) input.size) (by omega)
            (by have := Nat.min_le_right (64 - s.buffered.val) input.size; omega)).toList.length ≤ 64)]
          using hcopy
      rw [← hbuffer]
      simp only [compressList, Vector.toArray_toList]

/-- Canonical complete-block state, live buffer prefix, and wrapped counter. -/
def Represents (s : State) (xs : List UInt8) : Prop :=
  s.chaining = (absorb Ssz.Sha256.initialState xs).1 ∧
  s.buffer.toList.take s.buffered.val = (absorb Ssz.Sha256.initialState xs).2 ∧
  s.byteLen = UInt64.ofNat xs.length

theorem new_represents : Represents new [] := by
  simp [Represents, new]

theorem update_represents (s : State) (xs : List UInt8) (input : ByteArray)
    (h : Represents s xs) :
    Represents (update s input).state (xs ++ input.data.toList) := by
  obtain ⟨hc, hr, hn⟩ := h
  have hu := update_absorb s input
  rw [hc, hr, ← absorb_append] at hu
  refine ⟨congrArg Prod.fst hu, congrArg Prod.snd hu, ?_⟩
  rw [update_byteLen, hn, ← UInt64.ofNat_add]
  simp only [List.length_append, Array.length_toList, ByteArray.size_data]

theorem represents_buffered (s : State) (xs : List UInt8) (h : Represents s xs) :
    s.buffered.val = xs.length % 64 := by
  have hr := congrArg List.length h.2.1
  simpa only [List.length_take, Vector.length_toList,
    Nat.min_eq_left (Nat.le_of_lt s.buffered.isLt), absorb_residual_length] using hr

/-- Splitting an input does not change the represented logical stream. -/
theorem update_append_represents (s : State) (xs : List UInt8)
    (left right : ByteArray) (h : Represents s xs) :
    Represents (update (update s left).state right).state
      (xs ++ (left.data.toList ++ right.data.toList)) := by
  simpa only [List.append_assoc] using
    update_represents (update s left).state (xs ++ left.data.toList) right
      (update_represents s xs left h)

end SszNative.HashStream