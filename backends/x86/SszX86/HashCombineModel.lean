import SszX86.HashMemory
import SszHashStreamRefinement

namespace SszX86.Hash.Combine
open SszNative.HashStream

/-- A borrow of one full block from its original input allocation. -/
def inputBlock (input : ByteArray) (start : Nat) (bound : start + 64 ≤ input.size) :
    Vector UInt8 64 :=
  Vector.ofFn fun i => input[start + i.val]'(by have := i.isLt; omega)

theorem inputBlock_compress (chaining : Vector UInt32 8) (input : ByteArray)
    (start : Nat) (bound : start + 64 ≤ input.size) :
    compressBuffer chaining (inputBlock input start bound) =
      Ssz.Sha256.compress chaining input start := by
  unfold compressBuffer
  refine compress_locality chaining ⟨(inputBlock input start bound).toArray⟩ input
    0 start (by
      change 0 + 64 ≤ (inputBlock input start bound).toArray.size
      simp) bound ?_
  intro i hi
  simp only [ByteArray.getElem_eq_getElem_data, Nat.zero_add, inputBlock,
    Vector.getElem_toArray, Vector.getElem_ofFn]

/-- The exact residual copy, including the stale suffix, is the short-loop exit. -/
theorem drain_short (buffer : Vector UInt8 64) (chaining : Vector UInt32 8)
    (length : UInt64) (input : ByteArray) (start : Nat) (bound : start ≤ input.size)
    (short : input.size - start < 64) :
    (drain buffer chaining length input start bound).state =
      { buffer := copy buffer 0 input start (input.size - start) (by omega) (by omega)
        chaining := chaining
        buffered := ⟨input.size - start, short⟩
        byteLen := length } := by
  simp only [drain, Nat.div_eq_of_lt short, Nat.mod_eq_of_lt short,
    Nat.mul_zero, Nat.add_zero, List.range_zero, List.foldl_nil]

private theorem state_fields_eq (s t : State)
    (buffer : s.buffer = t.buffer) (chaining : s.chaining = t.chaining)
    (buffered : s.buffered = t.buffered) (byteLen : s.byteLen = t.byteLen) : s = t := by
  cases s
  cases t
  cases buffer
  cases chaining
  cases buffered
  cases byteLen
  rfl

/-- One direct block changes only the chaining words. In particular the
unwritten buffer tail is the same on both sides of this exact-state equality. -/
theorem drain_step (buffer : Vector UInt8 64) (chaining : Vector UInt32 8)
    (length : UInt64) (input : ByteArray) (start : Nat)
    (bound : start ≤ input.size) (full : start + 64 ≤ input.size) :
    (drain buffer chaining length input start bound).state =
      (drain buffer (Ssz.Sha256.compress chaining input start) length input
        (start + 64) (by omega)).state := by
  have rest : (input.size - start) % 64 = (input.size - (start + 64)) % 64 := by
    omega
  have stop : start + 64 * ((input.size - start) / 64) =
      start + 64 + 64 * ((input.size - (start + 64)) / 64) := by omega
  apply state_fields_eq
  · simp only [drain, rest, stop]
  · change (List.range ((input.size - start) / 64)).foldl
        (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) chaining =
      (List.range ((input.size - (start + 64)) / 64)).foldl
        (fun current i => Ssz.Sha256.compress current input (start + 64 + 64 * i))
        (Ssz.Sha256.compress chaining input start)
    rw [← absorb_drop_eq_rangeFold chaining input start bound,
      ← absorb_drop_eq_rangeFold (Ssz.Sha256.compress chaining input start)
        input (start + 64) (by omega)]
    rw [absorb_step chaining (input.data.toList.drop start) (by
      simp only [List.length_drop, Array.length_toList, ByteArray.size_data]
      omega), ← compress_eq_compressList chaining input start full, List.drop_drop]
  · apply Fin.ext
    exact rest
  · rfl

/-- Initializing the source counter directly to the left length is the first
update's required length addition, not a special case for fixed-size inputs. -/
theorem update_new (input : ByteArray) :
    (update new input).state =
      (drain new.buffer new.chaining (UInt64.ofNat input.size) input 0 (by omega)).state := by
  simp only [update, new_buffered, ↓reduceDIte, new_byteLen, UInt64.zero_add]

/-- The native empty-buffer path skips the buffered copy but still adds length. -/
theorem update_empty_buffer (state : State) (input : ByteArray)
    (empty : state.buffered.val = 0) :
    (update state input).state =
      (drain state.buffer state.chaining (state.byteLen + UInt64.ofNat input.size)
        input 0 (by omega)).state := by
  simp only [update, empty, ↓reduceDIte]

/-- CMOV's count is also sufficient to prove that the incomplete path consumed
all of the right input; the untouched tail remains exactly the old tail. -/
theorem update_incomplete (state : State) (input : ByteArray)
    (nonempty : state.buffered.val ≠ 0)
    (short : state.buffered.val + min (64 - state.buffered.val) input.size < 64) :
    (update state input).state =
      { buffer := copy state.buffer state.buffered.val input 0 input.size
          (by have := state.buffered.isLt; omega) (by omega)
        chaining := state.chaining
        buffered := ⟨state.buffered.val + input.size, by
          have := state.buffered.isLt
          omega⟩
        byteLen := state.byteLen + UInt64.ofNat input.size } := by
  have count : min (64 - state.buffered.val) input.size = input.size := by
    have := state.buffered.isLt
    omega
  simp only [update, nonempty, ↓reduceDIte]
  rw [dite_eq_left short]
  simp only [count]

/-- Completing the buffer feeds that very buffer to the real compression
interface, and subsequently drains only the original right allocation. -/
theorem update_complete (state : State) (input : ByteArray)
    (nonempty : state.buffered.val ≠ 0)
    (full : 64 ≤ state.buffered.val + min (64 - state.buffered.val) input.size) :
    (update state input).state =
      let count := 64 - state.buffered.val
      let buffer := copy state.buffer state.buffered.val input 0 count
        (by have := state.buffered.isLt; omega) (by have := state.buffered.isLt; omega)
      (drain buffer (compressBuffer state.chaining buffer)
        (state.byteLen + UInt64.ofNat input.size) input count
        (by have := state.buffered.isLt; omega)).state := by
  have count : min (64 - state.buffered.val) input.size = 64 - state.buffered.val := by
    have := state.buffered.isLt
    omega
  have notShort : ¬state.buffered.val + min (64 - state.buffered.val) input.size < 64 := by
    omega
  simp only [update, nonempty, ↓reduceDIte]
  rw [dite_eq_right notShort]
  simp only [count, compressBuffer]

end SszX86.Hash.Combine
