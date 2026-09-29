import SszHashStreamRefinement
import SszHashStreamMemory

set_option autoImplicit false

namespace SszNative.HashStream

/-- Repeated calls to the actual update model; every call retains its own
original input allocation and direct-block offsets. -/
def updates (s : State) : List ByteArray → State
  | [] => s
  | input :: rest => updates (update s input).state rest

/-- Logical concatenation used only by the specification, not by update. -/
def segmentBytes (chunks : List ByteArray) : List UInt8 :=
  chunks.flatMap (fun input => input.data.toList)

theorem updates_append (s : State) (front back : List ByteArray) :
    updates s (front ++ back) = updates (updates s front) back := by
  induction front generalizing s with
  | nil => rfl
  | cons input rest ih =>
      simpa only [List.cons_append, updates] using ih (update s input).state

theorem updates_represents (s : State) (xs : List UInt8)
    (chunks : List ByteArray) (h : Represents s xs) :
    Represents (updates s chunks) (xs ++ segmentBytes chunks) := by
  induction chunks generalizing s xs with
  | nil => simpa [updates, segmentBytes] using h
  | cons input rest ih =>
      have next := update_represents s xs input h
      have result := ih (update s input).state (xs ++ input.data.toList) next
      simpa only [updates, segmentBytes, List.flatMap_cons, List.append_assoc] using result

theorem new_updates_represents (chunks : List ByteArray) :
    Represents (updates new chunks) (segmentBytes chunks) := by
  simpa only [List.nil_append] using updates_represents new [] chunks new_represents

/-- Split input changes stale buffer cells, so the useful equivalence relates
only the chaining words, occupancy, counter, and initialized buffer prefix. -/
def StreamEquivalent (s t : State) : Prop :=
  s.chaining = t.chaining ∧ s.buffered = t.buffered ∧ s.byteLen = t.byteLen ∧
    s.buffer.toList.take s.buffered.val = t.buffer.toList.take t.buffered.val

theorem represents_streamEquivalent (s t : State) (xs : List UInt8)
    (hs : Represents s xs) (ht : Represents t xs) : StreamEquivalent s t := by
  refine ⟨hs.1.trans ht.1.symm, ?_, hs.2.2.trans ht.2.2.symm,
    hs.2.1.trans ht.2.1.symm⟩
  apply Fin.ext
  exact (represents_buffered s xs hs).trans (represents_buffered t xs ht).symm

/-- Arbitrary segmentation, including empty segments, preserves stream state
without incorrectly claiming equality of stale bytes. -/
theorem updates_segmentation (left right : List ByteArray)
    (sameBytes : segmentBytes left = segmentBytes right) :
    StreamEquivalent (updates new left) (updates new right) := by
  apply represents_streamEquivalent _ _ (segmentBytes left)
  · exact new_updates_represents left
  · rw [sameBytes]
    exact new_updates_represents right

theorem updates_wrapped_length (chunks : List ByteArray) :
    (updates new chunks).byteLen = UInt64.ofNat (segmentBytes chunks).length :=
  (new_updates_represents chunks).2.2

theorem updates_buffered (chunks : List ByteArray) :
    (updates new chunks).buffered.val = (segmentBytes chunks).length % 64 :=
  represents_buffered _ _ (new_updates_represents chunks)

/-- No public composition can manufacture a private buffer-bounds fault. -/
theorem updates_private_bounds (s : State) (chunks : List ByteArray) :
    (updates s chunks).buffered.val < 64 ∧
    (updates s chunks).buffer.toArray.size = 64 ∧
    (updates s chunks).chaining.toArray.size = 8 ∧
    (stateBytes (updates s chunks)).toArray.size = 112 := by
  exact ⟨buffered_bound _, by simp, by simp, by simp⟩

end SszNative.HashStream
