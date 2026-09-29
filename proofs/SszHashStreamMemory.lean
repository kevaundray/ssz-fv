import SszHashStream

set_option autoImplicit false

namespace SszNative.HashStream

/-- A byte of a little-endian native scalar. UInt8.ofNat selects its low eight
bits; the scalar's own width is already enforced by the source field type. -/
def littleByte (value lane : Nat) : UInt8 := UInt8.ofNat (value / 256 ^ lane)

/-- All 112 bytes, in the placement used by both native instruction streams.
There are no unspecified padding bytes or elided fields. -/
def stateBytes (s : State) : Vector UInt8 112 :=
  Vector.ofFn fun i =>
    if hb : i.val < 64 then s.buffer[i.val]
    else if hc : i.val < 96 then
      littleByte (s.chaining[(i.val - 64) / 4]'(by omega)).toNat ((i.val - 64) % 4)
    else if hi : i.val < 104 then
      littleByte s.buffered.val (i.val - 96)
    else littleByte s.byteLen.toNat (i.val - 104)

/-- The exact finite state footprint; bytes outside it are deliberately not
constrained by the representation relation. -/
def StateMemory (mem : Nat → UInt8) (base : Nat) (s : State) : Prop :=
  ∀ i : Fin 112, mem (base + i.val) = (stateBytes s)[i.val]

theorem stateBytes_size (s : State) : (stateBytes s).toArray.size = 112 := by simp

theorem stateBytes_buffer (s : State) (i : Nat) (hi : i < 64) :
    (stateBytes s)[i]'(by omega) = s.buffer[i] := by
  simp [stateBytes, hi]

theorem stateBytes_chaining (s : State) (i lane : Nat)
    (hi : i < 8) (hl : lane < 4) :
    (stateBytes s)[64 + 4 * i + lane]'(by omega) =
      littleByte s.chaining[i].toNat lane := by
  have hb : ¬ 64 + 4 * i + lane < 64 := by omega
  have hc : 64 + 4 * i + lane < 96 := by omega
  have hdiv : (64 + 4 * i + lane - 64) / 4 = i := by omega
  have hmod : (64 + 4 * i + lane - 64) % 4 = lane := by omega
  simp [stateBytes, hb, hc, hdiv, hmod]

theorem stateBytes_buffered (s : State) (lane : Nat) (hl : lane < 8) :
    (stateBytes s)[96 + lane]'(by omega) = littleByte s.buffered.val lane := by
  have hb : ¬ 96 + lane < 64 := by omega
  have hc : ¬ 96 + lane < 96 := by omega
  have hi : 96 + lane < 104 := by omega
  simp [stateBytes, hb, hc, hi]

theorem stateBytes_byteLen (s : State) (lane : Nat) (hl : lane < 8) :
    (stateBytes s)[104 + lane]'(by omega) = littleByte s.byteLen.toNat lane := by
  have hb : ¬ 104 + lane < 64 := by omega
  have hc : ¬ 104 + lane < 96 := by omega
  have hi : ¬ 104 + lane < 104 := by omega
  simp [stateBytes, hb, hc, hi]

theorem stateMemory_buffer (mem : Nat → UInt8) (base : Nat) (s : State)
    (hm : StateMemory mem base s) (i : Nat) (hi : i < 64) :
    mem (base + i) = s.buffer[i] := by
  exact (hm ⟨i, by omega⟩).trans (stateBytes_buffer s i hi)

theorem stateMemory_chaining (mem : Nat → UInt8) (base : Nat) (s : State)
    (hm : StateMemory mem base s) (i lane : Nat) (hi : i < 8) (hl : lane < 4) :
    mem (base + (64 + 4 * i + lane)) = littleByte s.chaining[i].toNat lane := by
  exact (hm ⟨64 + 4 * i + lane, by omega⟩).trans (stateBytes_chaining s i lane hi hl)

theorem stateMemory_buffered (mem : Nat → UInt8) (base : Nat) (s : State)
    (hm : StateMemory mem base s) (lane : Nat) (hl : lane < 8) :
    mem (base + (96 + lane)) = littleByte s.buffered.val lane := by
  exact (hm ⟨96 + lane, by omega⟩).trans (stateBytes_buffered s lane hl)

theorem stateMemory_byteLen (mem : Nat → UInt8) (base : Nat) (s : State)
    (hm : StateMemory mem base s) (lane : Nat) (hl : lane < 8) :
    mem (base + (104 + lane)) = littleByte s.byteLen.toNat lane := by
  exact (hm ⟨104 + lane, by omega⟩).trans (stateBytes_byteLen s lane hl)

/-- Buffer contents in the direct-block path depend only on the final remainder
copy. Chaining-state computation cannot overwrite or refresh its stale tail. -/
theorem drain_buffer_independent (buf : Vector UInt8 64)
    (first second : Vector UInt32 8) (firstLen secondLen : UInt64)
    (input : ByteArray) (start : Nat) (hs : start ≤ input.size) :
    (drain buf first firstLen input start hs).state.buffer =
      (drain buf second secondLen input start hs).state.buffer := rfl

/-- A split trace always exposes the wrapping length addition before any copy
or compression, including an empty-input update. -/
theorem update_length_first (s : State) (input : ByteArray) :
    (update s input).effects.head? = some (Effect.addLength (UInt64.ofNat input.size)) := by
  unfold update
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- The initial object has all its private accesses admitted, without a hidden
alternative initializer or successful-hash premise. -/
theorem new_private_bounds : new.buffered.val < 64 ∧ new.buffer.toArray.size = 64 ∧
    new.chaining.toArray.size = 8 ∧ (stateBytes new).toArray.size = 112 := by
  simp [new]

/-- The same complete bounds hold after every public update, independently of
the input's physical or logical width. -/
theorem update_private_bounds (s : State) (input : ByteArray) :
    (update s input).state.buffered.val < 64 ∧
    (update s input).state.buffer.toArray.size = 64 ∧
    (update s input).state.chaining.toArray.size = 8 ∧
    (stateBytes (update s input).state).toArray.size = 112 := by
  exact ⟨buffered_bound _, by simp, by simp, by simp⟩

end SszNative.HashStream
