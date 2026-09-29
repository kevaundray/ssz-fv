import SszHashStreamRefinement
import SszHashStreamPaddingWrites
import Ssz.Merkle.Tree

set_option autoImplicit false

namespace SszNative.HashStream

/-- The consuming finalizer's ordered native operations. Every mutable range
carries its access bound; the fixed length and digest ranges are intrinsic. -/
inductive FinalEffect where
  | writeDelimiter (index : Fin 64)
  | zero (start count : Nat) (bound : start + count ≤ 64)
  | compressBuffer
  | resetBuffered
  | writeLength (byteLen : UInt64)
  | emitDigest

/-- Unlike update, finalization returns no reusable streaming state. The last
buffer and chaining value are exposed solely as execution witnesses. -/
structure FinalResult where
  buffer : Vector UInt8 64
  chaining : Vector UInt32 8
  effects : List FinalEffect

/-- The delimiter write preserves all other cells, including the stale tail. -/
def delimiterBuffer (s : State) : Vector UInt8 64 :=
  overwrite s.buffer s.buffered.val [0x80] (by
    simp only [List.length_cons, List.length_nil]
    have h := s.buffered.isLt
    omega)

/-- The first block in the two-block case clears the entire remaining suffix. -/
def overflowBuffer (s : State) : Vector UInt8 64 :=
  overwrite (delimiterBuffer s) (s.buffered.val + 1)
    (List.replicate (64 - (s.buffered.val + 1)) 0) (by
      simp only [List.length_replicate]
      have h := s.buffered.isLt
      omega)

/-- Zero to byte 56, then overwrite all eight length bytes. -/
def finishBuffer (buf : Vector UInt8 64) (pos : Nat) (bound : pos ≤ 56)
    (byteLen : UInt64) : Vector UInt8 64 :=
  let cleared := overwrite buf pos (List.replicate (56 - pos) 0) (by
    simp only [List.length_replicate]
    omega)
  overwrite cleared 56 (finalLengthBytes byteLen) (by simp)

/-- Compression always receives an actual, complete 64-byte native buffer. -/
def compressBuffer (chaining : Vector UInt32 8) (buf : Vector UInt8 64) :
    Vector UInt32 8 :=
  Ssz.Sha256.compress chaining ⟨buf.toArray⟩ 0

/-- Literal consuming source orchestration, including the delimiter-before-test
order and the reset after an overflowing first padding block. -/
def finalizeRun (s : State) : FinalResult :=
  if spill : 56 < s.buffered.val + 1 then
    let first := overflowBuffer s
    let next := compressBuffer s.chaining first
    let last := finishBuffer first 0 (by omega) s.byteLen
    { buffer := last
      chaining := compressBuffer next last
      effects := [.writeDelimiter s.buffered,
        .zero (s.buffered.val + 1) (64 - (s.buffered.val + 1)) (by
          have h := s.buffered.isLt
          omega),
        .compressBuffer, .resetBuffered, .zero 0 56 (by omega),
        .writeLength s.byteLen, .compressBuffer, .emitDigest] }
  else
    let last := finishBuffer (delimiterBuffer s) (s.buffered.val + 1)
      (by omega) s.byteLen
    { buffer := last
      chaining := compressBuffer s.chaining last
      effects := [.writeDelimiter s.buffered,
        .zero (s.buffered.val + 1) (56 - (s.buffered.val + 1)) (by omega),
        .writeLength s.byteLen, .compressBuffer, .emitDigest] }

/-- The pinned big-endian word emission, with every word access checked. -/
def finalize (s : State) : ByteArray :=
  Ssz.Sha256.digest (finalizeRun s).chaining

/-- One update, followed by consumption. -/
def hash (input : ByteArray) : ByteArray :=
  finalize (update new input).state

/-- Two updates on the original raw allocations: no chunk-width assumption. -/
def combine (left right : ByteArray) : ByteArray :=
  finalize (update (update new left).state right).state

theorem delimiterBuffer_prefix (s : State) :
    (delimiterBuffer s).toList.take (s.buffered.val + 1) =
      s.buffer.toList.take s.buffered.val ++ [0x80] := by
  simpa only [delimiterBuffer, List.length_cons, List.length_nil] using
    overwrite_take_end s.buffer s.buffered.val [0x80] (by
      simp only [List.length_cons, List.length_nil]
      have h := s.buffered.isLt
      omega)

theorem overflowBuffer_toList (s : State) :
    (overflowBuffer s).toList =
      s.buffer.toList.take s.buffered.val ++ [0x80] ++
        List.replicate (63 - s.buffered.val) 0 := by
  unfold overflowBuffer
  rw [overwrite_toList_end]
  · rw [delimiterBuffer_prefix]
    have count : 64 - (s.buffered.val + 1) = 63 - s.buffered.val := by omega
    rw [count]
  · simp only [List.length_replicate]
    have h := s.buffered.isLt
    omega

theorem finishBuffer_toList (buf : Vector UInt8 64) (pos : Nat)
    (bound : pos ≤ 56) (byteLen : UInt64) :
    (finishBuffer buf pos bound byteLen).toList =
      buf.toList.take pos ++ List.replicate (56 - pos) 0 ++ finalLengthBytes byteLen := by
  unfold finishBuffer
  rw [overwrite_toList_end]
  · have endpoint : pos + (List.replicate (56 - pos) (0 : UInt8)).length = 56 := by
      simp only [List.length_replicate]
      omega
    have cleared := overwrite_take_end buf pos
      (List.replicate (56 - pos) (0 : UInt8)) (by
        simp only [List.length_replicate]
        omega)
    simp only [endpoint] at cleared
    rw [cleared]
  · simp

theorem finishBuffer_delimiter (s : State) (bound : s.buffered.val + 1 ≤ 56) :
    (finishBuffer (delimiterBuffer s) (s.buffered.val + 1) bound s.byteLen).toList =
      s.buffer.toList.take s.buffered.val ++ [0x80] ++
        List.replicate (55 - s.buffered.val) 0 ++ finalLengthBytes s.byteLen := by
  rw [finishBuffer_toList, delimiterBuffer_prefix]
  have count : 56 - (s.buffered.val + 1) = 55 - s.buffered.val := by omega
  rw [count]

theorem finishBuffer_reset (buf : Vector UInt8 64) (byteLen : UInt64) :
    (finishBuffer buf 0 (by omega) byteLen).toList =
      List.replicate 56 0 ++ finalLengthBytes byteLen := by
  simp only [finishBuffer_toList, List.take_zero, Nat.sub_zero, List.nil_append]

theorem compressBuffer_eq (chaining : Vector UInt32 8) (buf : Vector UInt8 64) :
    compressBuffer chaining buf = compressList chaining buf.toList := by
  simp only [compressBuffer, compressList, Vector.toArray_toList]

/-- Finalization overwrites every byte after the live prefix; no stale byte
can reach either compression. The result is exactly one or two padded blocks. -/
theorem finalizeRun_chaining (s : State) :
    (finalizeRun s).chaining =
      (absorb s.chaining
        (residualPad (s.buffer.toList.take s.buffered.val) s.byteLen)).1 := by
  have liveLength : (s.buffer.toList.take s.buffered.val).length = s.buffered.val := by
    simp only [List.length_take, Vector.length_toList]
    exact Nat.min_eq_left (by have h := s.buffered.isLt; omega)
  unfold finalizeRun
  split
  · rename_i spill
    rw [residualPad_two _ _ (by omega) (by rw [liveLength]; exact s.buffered.isLt),
      absorb_block_append _ _ _ (residualPad_two_first_length _ (by
        rw [liveLength]
        exact s.buffered.isLt)),
      absorb_block _ _ (residualPad_two_last_length s.byteLen)]
    simp only [compressBuffer_eq, overflowBuffer_toList, finishBuffer_reset, liveLength]
  · rename_i small
    rw [residualPad_one _ _ (by omega), absorb_block]
    · simp only [compressBuffer_eq, finishBuffer_delimiter, liveLength]
    · simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate, finalLengthBytes_length, liveLength]
      omega

/-- The reference hash factors at the same residual, for arbitrary natural
message lengths, retaining the pinned modulo-2^64 bit count. -/
theorem reference_hash_residual (input : ByteArray) :
    Ssz.Sha256.hash input = Ssz.Sha256.digest
      (absorb (absorb Ssz.Sha256.initialState input.data.toList).1
        (residualPad (absorb Ssz.Sha256.initialState input.data.toList).2
          (UInt64.ofNat input.size))).1 := by
  have residualLength :
      (absorb Ssz.Sha256.initialState input.data.toList).2.length = input.size % 64 := by
    rw [absorb_residual_eq_drop]
    simp only [List.length_drop, Array.length_toList]
    change input.size - 64 * (input.size / 64) = input.size % 64
    omega
  rw [hash_eq_absorb_pad, pad_toList]
  simp only [List.append_assoc]
  rw [absorb_append]
  simp only [residualPad, residualLength, paddingZeros_eq, finalLengthBytes_ofNat,
    List.append_assoc]

/-- Public finalization requires only the present streaming invariant, never a
future execution result or a hash oracle. -/
theorem finalize_eq_hash (s : State) (input : ByteArray)
    (represents : Represents s input.data.toList) :
    finalize s = Ssz.Sha256.hash input := by
  rw [reference_hash_residual]
  unfold finalize
  rw [finalizeRun_chaining, represents.1, represents.2.1, represents.2.2]
  rfl

theorem hash_eq (input : ByteArray) : hash input = Ssz.Sha256.hash input := by
  apply finalize_eq_hash
  simpa only [List.nil_append] using update_represents new [] input new_represents

/-- Raw left and right arrays may have any widths, including zero. -/
theorem combine_eq_hash (left right : ByteArray) :
    combine left right = Ssz.Sha256.hash (left ++ right) := by
  apply finalize_eq_hash
  have first := update_represents new [] left new_represents
  have second := update_represents (update new left).state left.data.toList right
    (by simpa only [List.nil_append] using first)
  simpa using second

/-- The pinned SSZ operation hashes actual concatenation, not two fixed chunks. -/
theorem combine_eq (left right : Ssz.Bytes) :
    (combine ⟨left⟩ ⟨right⟩).data = Ssz.combine left right := by
  have joined : (ByteArray.mk left ++ ByteArray.mk right) = ByteArray.mk (left ++ right) := by
    apply ByteArray.ext
    simp only [ByteArray.data_append]
  rw [combine_eq_hash, joined, Ssz.combine]

@[simp] theorem finalize_size (s : State) : (finalize s).size = 32 := by
  exact digest_size _

@[simp] theorem native_hash_size (input : ByteArray) : (hash input).size = 32 :=
  finalize_size _

@[simp] theorem combine_size (left right : ByteArray) : (combine left right).size = 32 :=
  finalize_size _

/-- A consumed stale suffix has no effect on the output, even for states not
constructed by the public initializer. -/
theorem finalize_live_prefix (s t : State)
    (chaining : s.chaining = t.chaining)
    (live : s.buffer.toList.take s.buffered.val = t.buffer.toList.take t.buffered.val)
    (length : s.byteLen = t.byteLen) : finalize s = finalize t := by
  unfold finalize
  rw [finalizeRun_chaining, finalizeRun_chaining, chaining, live, length]

theorem compressBuffer_source_safe (buf : Vector UInt8 64) :
    0 + 64 ≤ (ByteArray.mk buf.toArray).size := by
  simp [ByteArray.size]

/-- Safety includes both one- and two-block branches and fixed digest emission. -/
def FinalEffect.Safe : FinalEffect → Prop
  | .writeDelimiter index => index.val < 64
  | .zero start count _ => start + count ≤ 64
  | .compressBuffer => 0 + 64 ≤ 64
  | .resetBuffered => True
  | .writeLength _ => 56 + 8 ≤ 64
  | .emitDigest => (∀ i : Fin 32, i.val / 4 < 8)

theorem finalEffect_safe (effect : FinalEffect) : effect.Safe := by
  cases effect with
  | writeDelimiter index => exact index.isLt
  | zero _ _ bound => exact bound
  | compressBuffer => exact Nat.le_refl 64
  | resetBuffered => trivial
  | writeLength _ => exact Nat.le_refl 64
  | emitDigest => intro i; have h := i.isLt; omega

theorem finalize_effects_safe (s : State) :
    ∀ effect ∈ (finalizeRun s).effects, effect.Safe := by
  intro effect _
  exact finalEffect_safe effect

end SszNative.HashStream
