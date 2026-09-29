import Ssz.Hash.Sha256

set_option autoImplicit false

namespace SszNative.HashStream

/-- The four fields occupying the native 112-byte object. The index type
excludes precisely the private states that cannot arise at an API boundary. -/
structure State where
  buffer : Vector UInt8 64
  chaining : Vector UInt32 8
  buffered : Fin 64
  byteLen : UInt64

/-- Actual field placement shared by both native architectures. -/
def stateFields : List (Nat × Nat) := [(0, 64), (64, 32), (96, 8), (104, 8)]

theorem state_footprint :
    stateFields = [(0, 64), (64, 32), (96, 8), (104, 8)] ∧
    0 + 64 = 64 ∧ 64 + 32 = 96 ∧ 96 + 8 = 104 ∧ 104 + 8 = 112 := by
  simp [stateFields]

/-- Copies name the original input, not an allocated substring. Bounds are
part of each effect, so there is no unchecked trace or defaulting read. -/
inductive Effect (inputSize : Nat) where
  | addLength (amount : UInt64)
  | copy (src dst count : Nat)
      (inputBound : src + count ≤ inputSize) (bufferBound : dst + count ≤ 64)
  | compressBuffer
  | compressInput (src : Nat) (inputBound : src + 64 ≤ inputSize)

structure UpdateResult (inputSize : Nat) where
  state : State
  effects : List (Effect inputSize)

/-- An in-bounds interval overwrite; every cell outside the destination
interval, including the stale suffix, is preserved verbatim. -/
def copy (buf : Vector UInt8 64) (dst : Nat) (input : ByteArray)
    (src count : Nat) (_destBound : dst + count ≤ 64)
    (sourceBound : src + count ≤ input.size) : Vector UInt8 64 :=
  Vector.ofFn fun i =>
    if inside : dst ≤ i.val ∧ i.val < dst + count then
      input[src + (i.val - dst)]'(by omega)
    else buf[i.val]

@[simp] theorem copy_inside (buf : Vector UInt8 64) (dst : Nat)
    (input : ByteArray) (src count : Nat) (hd : dst + count ≤ 64)
    (hs : src + count ≤ input.size) (i : Nat) (hi : i < 64)
    (inside : dst ≤ i ∧ i < dst + count) :
    (copy buf dst input src count hd hs)[i] =
      input[src + (i - dst)]'(by omega) := by
  simp [copy, inside]

@[simp] theorem copy_outside (buf : Vector UInt8 64) (dst : Nat)
    (input : ByteArray) (src count : Nat) (hd : dst + count ≤ 64)
    (hs : src + count ≤ input.size) (i : Nat) (hi : i < 64)
    (outside : ¬ (dst ≤ i ∧ i < dst + count)) :
    (copy buf dst input src count hd hs)[i] = buf[i] := by
  simp [copy, outside]

theorem copy_stale_tail (buf : Vector UInt8 64) (dst : Nat)
    (input : ByteArray) (src count : Nat) (hd : dst + count ≤ 64)
    (hs : src + count ≤ input.size) (i : Nat) (hi : i < 64)
    (afterWrite : dst + count ≤ i) :
    (copy buf dst input src count hd hs)[i] = buf[i] := by
  apply copy_outside
  omega

/-- The exact source initializer, including all 64 initially zero buffer cells. -/
def new : State :=
  { buffer := Vector.replicate 64 0
    chaining := Ssz.Sha256.initialState
    buffered := ⟨0, by decide⟩
    byteLen := 0 }

/-- Drain only complete blocks directly from the original input, then copy the
remaining bytes to the buffer prefix. No direct block is copied into `buf`. -/
def drain (buf : Vector UInt8 64) (chaining : Vector UInt32 8)
    (byteLen : UInt64) (input : ByteArray) (start : Nat)
    (startBound : start ≤ input.size) : UpdateResult input.size :=
  let count := (input.size - start) / 64
  let rest := (input.size - start) % 64
  let stop := start + 64 * count
  have restBound : rest < 64 := Nat.mod_lt _ (by decide)
  have split := Nat.mod_add_div (input.size - start) 64
  have sourceBound : stop + rest ≤ input.size := by omega
  { state :=
      { buffer := copy buf 0 input stop rest (by omega) sourceBound
        chaining := (List.range count).foldl
          (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) chaining
        buffered := ⟨rest, restBound⟩
        byteLen := byteLen }
    effects := (List.finRange count).map (fun i =>
      Effect.compressInput (start + 64 * i.val) (by
        have indexBound := i.isLt
        omega)) ++
      [Effect.copy stop 0 rest sourceBound (by omega)] }

/-- Literal buffered/direct-block update orchestration. The length addition is
first, including empty updates, and uses the native wrapping UInt64 operation. -/
def update (s : State) (input : ByteArray) : UpdateResult input.size :=
  let byteLen := s.byteLen + UInt64.ofNat input.size
  if empty : s.buffered.val = 0 then
    let out := drain s.buffer s.chaining byteLen input 0 (by omega)
    { state := out.state
      effects := Effect.addLength (UInt64.ofNat input.size) :: out.effects }
  else
    let count := min (64 - s.buffered.val) input.size
    have bufferBound : s.buffered.val + count ≤ 64 := by
      have hb := s.buffered.isLt
      have hc := Nat.min_le_left (64 - s.buffered.val) input.size
      omega
    have inputBound : 0 + count ≤ input.size := by
      simpa using Nat.min_le_right (64 - s.buffered.val) input.size
    let buf := copy s.buffer s.buffered.val input 0 count bufferBound inputBound
    if incomplete : s.buffered.val + count < 64 then
      { state :=
          { buffer := buf
            chaining := s.chaining
            buffered := ⟨s.buffered.val + count, incomplete⟩
            byteLen := byteLen }
        effects := [Effect.addLength (UInt64.ofNat input.size),
          Effect.copy 0 s.buffered.val count inputBound bufferBound] }
    else
      let next := Ssz.Sha256.compress s.chaining ⟨buf.toArray⟩ 0
      let out := drain buf next byteLen input count (by omega)
      { state := out.state
        effects := Effect.addLength (UInt64.ofNat input.size) ::
          Effect.copy 0 s.buffered.val count inputBound bufferBound ::
          Effect.compressBuffer :: out.effects }

/-- Every public state has a legal delimiter-write index. -/
theorem buffered_bound (s : State) : s.buffered.val < 64 := s.buffered.isLt

theorem new_buffered : new.buffered.val = 0 := rfl

theorem new_byteLen : new.byteLen = 0 := rfl

theorem new_chaining : new.chaining = Ssz.Sha256.initialState := rfl

theorem new_buffer_zero (i : Nat) (hi : i < 64) : new.buffer[i] = 0 := by
  simp [new]

@[simp] theorem drain_byteLen (buf : Vector UInt8 64)
    (chaining : Vector UInt32 8) (byteLen : UInt64) (input : ByteArray)
    (start : Nat) (hs : start ≤ input.size) :
    (drain buf chaining byteLen input start hs).state.byteLen = byteLen := rfl

@[simp] theorem update_byteLen (s : State) (input : ByteArray) :
    (update s input).state.byteLen = s.byteLen + UInt64.ofNat input.size := by
  unfold update
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem update_buffered_bound (s : State) (input : ByteArray) :
    (update s input).state.buffered.val < 64 :=
  (update s input).state.buffered.isLt

/-- Extract the useful arithmetic promises from a recorded operation. -/
def Effect.Safe {inputSize : Nat} : Effect inputSize → Prop
  | .addLength _ => True
  | .copy src dst count _ _ => src + count ≤ inputSize ∧ dst + count ≤ 64
  | .compressBuffer => True
  | .compressInput src _ => src + 64 ≤ inputSize

theorem effect_safe {inputSize : Nat} (effect : Effect inputSize) : effect.Safe := by
  cases effect with
  | addLength => trivial
  | copy _ _ _ hs hd => exact ⟨hs, hd⟩
  | compressBuffer => trivial
  | compressInput _ hs => exact hs

theorem update_effects_safe (s : State) (input : ByteArray) :
    ∀ effect ∈ (update s input).effects, effect.Safe := by
  intro effect _
  exact effect_safe effect

/-- Direct-block processing leaves the old tail intact after the final copy. -/
theorem drain_stale_tail (buf : Vector UInt8 64)
    (chaining : Vector UInt32 8) (byteLen : UInt64) (input : ByteArray)
    (start : Nat) (hs : start ≤ input.size) (i : Nat) (hi : i < 64)
    (afterWrite : (input.size - start) % 64 ≤ i) :
    (drain buf chaining byteLen input start hs).state.buffer[i] = buf[i] := by
  exact copy_stale_tail buf 0 input (start + 64 * ((input.size - start) / 64))
    ((input.size - start) % 64) (by omega) (by omega) i hi (by omega)

end SszNative.HashStream
