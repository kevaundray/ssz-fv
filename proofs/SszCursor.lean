import Ssz.Proofs.Codec.Table
import SszLimbs

/-! Abstract cursor-write algorithm theorems.

These lemmas model byte-wise cursor updates on Nat-indexed memory. They are
representation proofs, not native ISA or Rust control-flow refinement. -/

set_option autoImplicit false

namespace SszNative.Cursor

open Ssz

abbrev Memory := Nat → UInt8

/-- Overwrite one byte interval `[start, start + data.size)` and leave the rest
unchanged. -/
def writeBlock (mem : Memory) (start : Nat) (data : Bytes) : Memory :=
  fun i =>
    if h₀ : i < start then mem i
    else if h₁ : i < start + data.size then
      data[(i - start)]'(by omega)
    else mem i

/-- Four little-endian offset bytes written by the cursor model. -/
def offsetBytes (body : Nat) : Bytes :=
  Array.ofFn (fun i : Fin bytesPerOffset =>
    UInt8.ofNat ((body / 2 ^ (8 * i.1)) % 256))

/-- The cursor loop over fixed/variable slots. -/
def writeCursor : List (Bool × Bytes) → Nat → Nat → Memory → Nat × Nat × Memory
  | [], head, body, mem => (head, body, mem)
  | (true, part) :: rest, head, body, mem =>
      writeCursor rest (head + part.size) body (writeBlock mem head part)
  | (false, part) :: rest, head, body, mem =>
      writeCursor rest (head + bytesPerOffset) (body + part.size)
        (writeBlock (writeBlock mem head (offsetBytes body)) body part)

/-- Zipping the pair projections of a slot list recovers the same slot list. -/
theorem zip_map_fst_snd (slots : List (Bool × Bytes)) :
    (slots.map Prod.fst).zip (slots.map Prod.snd) = slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      cases slot with
      | mk inline part => simp [ih]

/-- A byte written before the interval starts is unchanged. -/
theorem writeBlock_eq_of_lt (mem : Memory) (start : Nat) (data : Bytes) (i : Nat)
    (h : i < start) :
    writeBlock mem start data i = mem i := by
  simp [writeBlock, h]

/-- A byte written after the interval ends is unchanged. -/
theorem writeBlock_eq_of_ge (mem : Memory) (start : Nat) (data : Bytes) (i : Nat)
    (h : start + data.size ≤ i) :
    writeBlock mem start data i = mem i := by
  have hlt : ¬ i < start + data.size := Nat.not_lt.mpr h
  have h₀ : ¬ i < start := by omega
  simp [writeBlock, h₀, hlt]

/-- A byte inside the interval is overwritten by the payload byte at the
corresponding offset. -/
theorem writeBlock_eq_of_in (mem : Memory) (start : Nat) (data : Bytes) (i : Nat)
    (h₀ : start ≤ i) (h₁ : i < start + data.size) :
    writeBlock mem start data i = data[(i - start)]'(by omega) := by
  have hlt : ¬ i < start := by omega
  simp [writeBlock, hlt, h₁]

@[simp] theorem writeBlock_empty (mem : Memory) (start : Nat) :
    writeBlock mem start #[] = mem := by
  funext i
  by_cases before : i < start <;> simp [writeBlock, before]

/-- Two disjoint writes commute. -/
theorem writeBlock_commute (mem : Memory) (start₁ start₂ : Nat) (a b : Bytes)
    (h : start₁ + a.size ≤ start₂) :
    writeBlock (writeBlock mem start₁ a) start₂ b
      = writeBlock (writeBlock mem start₂ b) start₁ a := by
  funext i
  by_cases h₀ : i < start₁
  · simp [writeBlock, h₀]
  · have h₀' : start₁ ≤ i := Nat.le_of_not_lt h₀
    by_cases h₁ : i < start₁ + a.size
    · have h₂ : i < start₂ := by omega
      simp [writeBlock, h₀, h₁, h₂]
    · simp [writeBlock, h₀, h₁]

/-- Adjacent writes compose to one longer write. -/
theorem writeBlock_append (mem : Memory) (start : Nat) (front back : Bytes) :
    writeBlock (writeBlock mem start front) (start + front.size) back
      = writeBlock mem start (front ++ back) := by
  funext i
  by_cases h₀ : i < start
  · have before : i < start + front.size := by omega
    simp [writeBlock, h₀, before]
  · have h₀' : start ≤ i := Nat.le_of_not_lt h₀
    by_cases h₁ : i < start + front.size
    · have hfront : i - start < front.size := by omega
      have inside : i < start + (front ++ back).size := by
        simp only [Array.size_append]
        omega
      rw [writeBlock_eq_of_lt _ _ _ _ h₁,
        writeBlock_eq_of_in _ _ _ _ h₀' h₁,
        writeBlock_eq_of_in _ _ _ _ h₀' inside]
      simp [hfront]
    · have h₂ : start + front.size ≤ i := by omega
      by_cases h₃ : i < start + front.size + back.size
      · have inside : i < start + (front ++ back).size := by
          simp only [Array.size_append]
          omega
        have afterFront : ¬ i - start < front.size := by omega
        rw [writeBlock_eq_of_in _ _ _ _ h₂ h₃,
          writeBlock_eq_of_in _ _ _ _ h₀' inside]
        simp [Array.getElem_append, afterFront] <;> congr 1 <;> omega
      · have afterAll : start + (front ++ back).size ≤ i := by
          simp only [Array.size_append]
          omega
        rw [writeBlock_eq_of_ge _ _ _ _ (by omega),
          writeBlock_eq_of_ge _ _ _ _ h₂,
          writeBlock_eq_of_ge _ _ _ _ afterAll]

/-- The four cursor-offset bytes agree with the upstream little-endian integer
encoding. -/
theorem offsetBytes_eq_uintBytes (body : Nat) :
    offsetBytes body = Ssz.uintBytes bytesPerOffset body := by
  apply Array.ext
  · simp [offsetBytes, Ssz.uintBytes_size]
  · intro i hi _
    have hi' : i < bytesPerOffset := by simpa [offsetBytes, Array.size_ofFn] using hi
    simp only [offsetBytes, Array.getElem_ofFn]
    rw [SszNative.Limbs.uintBytes_byte bytesPerOffset body i hi']

/-- The cursor loop returns the expected final cursors and the expected framed
memory image. -/
theorem writeCursor_spec :
    ∀ (slots : List (Bool × Bytes)) (head body : Nat) (mem : Memory),
      head + headWidth slots ≤ body →
      writeCursor slots head body mem =
        (head + headWidth slots, body + bodyWidth slots,
          writeBlock (writeBlock mem head (headOf body slots)) body (bodiesOf slots)) := by
  intro slots
  induction slots with
  | nil =>
      intro head body mem h
      simp [writeCursor, headWidth, bodyWidth, headOf, bodiesOf]
  | cons slot rest ih =>
      intro head body mem h
      cases slot with
      | mk inline part =>
          cases inline with
          | true =>
              have hrest : head + part.size + headWidth rest ≤ body := by
                simpa [headWidth, Nat.add_assoc] using h
              have ih' := ih (head + part.size) body (writeBlock mem head part) hrest
              simpa [writeCursor, headWidth, bodyWidth, headOf, bodiesOf,
                writeBlock_append, Nat.add_assoc] using ih'
          | false =>
              have hcomm : head + bytesPerOffset + (headOf (body + part.size) rest).size ≤ body := by
                simpa [headWidth, Ssz.headOf_size, Nat.add_assoc] using h
              have hrest : head + bytesPerOffset + headWidth rest ≤ body + part.size := by
                simp [headWidth] at h
                omega
              have ih' := ih (head + bytesPerOffset) (body + part.size)
                (writeBlock (writeBlock mem head (offsetBytes body)) body part) hrest
              have ih'' := ih'
              rw [← writeBlock_commute (mem := writeBlock mem head (offsetBytes body))
                (start₁ := head + bytesPerOffset) (start₂ := body)
                (a := headOf (body + part.size) rest) (b := part) hcomm] at ih''
              have joined := writeBlock_append mem head
                (uintBytes bytesPerOffset body) (headOf (body + part.size) rest)
              simp only [uintBytes_size] at joined
              simpa [writeCursor, headWidth, bodyWidth, headOf, bodiesOf,
                offsetBytes_eq_uintBytes, writeBlock_append, joined, Nat.add_assoc] using ih''

theorem writeCursor_outside (slots : List (Bool × Bytes)) (head body : Nat) (mem : Memory)
    (h : head + headWidth slots ≤ body)
    (i : Nat) (hhead : i < head ∨ head + headWidth slots ≤ i)
    (hbody : i < body ∨ body + bodyWidth slots ≤ i) :
    (writeCursor slots head body mem).2.2 i = mem i := by
  have spec := writeCursor_spec slots head body mem h
  rw [spec]
  change writeBlock (writeBlock mem head (headOf body slots)) body (bodiesOf slots) i = mem i
  rcases hhead with hhead | hhead
  · have hlt : i < body := by omega
    have houter : writeBlock (writeBlock mem head (headOf body slots)) body (bodiesOf slots) i =
        writeBlock mem head (headOf body slots) i := by
      exact writeBlock_eq_of_lt _ _ _ _ hlt
    rw [houter]
    have hinner : writeBlock mem head (headOf body slots) i = mem i := by
      exact writeBlock_eq_of_lt _ _ _ _ hhead
    rw [hinner]
  · rcases hbody with hbody | hbody
    · have houter : writeBlock (writeBlock mem head (headOf body slots)) body (bodiesOf slots) i =
        writeBlock mem head (headOf body slots) i := by
        exact writeBlock_eq_of_lt _ _ _ _ hbody
      rw [houter]
      have hheader : head + (headOf body slots).size ≤ i := by
        simpa [Ssz.headOf_size] using hhead
      have hinner : writeBlock mem head (headOf body slots) i = mem i := by
        exact writeBlock_eq_of_ge _ _ _ _ hheader
      rw [hinner]
    · have hbody' : body + (bodiesOf slots).size ≤ i := by
        simpa [Ssz.bodiesOf_size] using hbody
      have houter : writeBlock (writeBlock mem head (headOf body slots)) body (bodiesOf slots) i =
        writeBlock mem head (headOf body slots) i := by
        exact writeBlock_eq_of_ge _ _ _ _ hbody'
      rw [houter]
      have hheader : head + (headOf body slots).size ≤ i := by
        simpa [Ssz.headOf_size] using hhead
      have hinner : writeBlock mem head (headOf body slots) i = mem i := by
        exact writeBlock_eq_of_ge _ _ _ _ hheader
      rw [hinner]

/-- The model memory read back as bytes is exactly the contiguous header/body
encoding, regardless of the original output-buffer contents. -/
theorem writeCursor_readout (slots : List (Bool × Bytes)) (mem : Memory) :
    Array.ofFn (fun i : Fin (headWidth slots + bodyWidth slots) =>
      (writeCursor slots 0 (headWidth slots) mem).2.2 i.1)
        = headOf (headWidth slots) slots ++ bodiesOf slots := by
  rw [writeCursor_spec slots 0 (headWidth slots) mem (by omega)]
  have joined := writeBlock_append mem 0 (headOf (headWidth slots) slots) (bodiesOf slots)
  simp only [headOf_size, Nat.zero_add] at joined
  simp only [joined]
  apply Array.ext
  · simp [headOf_size, bodiesOf_size]
  · intro i hi _
    simp only [Array.getElem_ofFn]
    rw [writeBlock_eq_of_in _ _ _ _ (Nat.zero_le i) (by
      simp only [Array.size_ofFn] at hi
      simpa only [Array.size_append, headOf_size, bodiesOf_size, Nat.zero_add] using hi)]
    simp

/-- The mixed-slot cursor model specializes to the upstream `assemble` output. -/
theorem writeCursor_assemble (slots : List (Bool × Bytes)) (mem : Memory)
    (h : headWidth slots + bodyWidth slots < 2 ^ (8 * bytesPerOffset)) :
    Ssz.assemble (slots.map Prod.fst) (slots.map Prod.snd)
      = .ok (Array.ofFn (fun i : Fin (headWidth slots + bodyWidth slots) =>
          (writeCursor slots 0 (headWidth slots) mem).2.2 i.1)) := by
  rw [writeCursor_readout]
  simp [Ssz.assemble, zip_map_fst_snd, Nat.not_le.mpr h] <;> rfl

/-- The native all-fixed fast path uses only one output cursor. -/
def writeInline : List Bytes → Nat → Memory → Nat × Memory
  | [], position, mem => (position, mem)
  | part :: rest, position, mem =>
      writeInline rest (position + part.size) (writeBlock mem position part)

theorem writeInline_cursor (parts : List Bytes) (head body : Nat) (mem : Memory) :
    writeCursor (parts.map fun part => (true, part)) head body mem =
      ((writeInline parts head mem).1, body, (writeInline parts head mem).2) := by
  induction parts generalizing head mem with
  | nil => rfl
  | cons part rest ih => simp only [List.map_cons, writeCursor, writeInline, ih]

theorem writeInline_end (parts : List Bytes) (head : Nat) (mem : Memory) :
    (writeInline parts head mem).1 =
      head + headWidth (parts.map fun part => (true, part)) := by
  induction parts generalizing head mem with
  | nil => rfl
  | cons part rest ih => simp [writeInline, ih, headWidth, Nat.add_assoc]

/-- The separately modeled sequential fast path produces the same SSZ output. -/
theorem writeInline_assemble (parts : List Bytes) (mem : Memory)
    (h : headWidth (parts.map fun part => (true, part)) +
        bodyWidth (parts.map fun part => (true, part)) < 2 ^ (8 * bytesPerOffset)) :
    Ssz.assemble (List.replicate parts.length true) parts
      = .ok (Array.ofFn (fun i : Fin (headWidth (parts.map fun part => (true, part)) +
          bodyWidth (parts.map fun part => (true, part))) =>
        (writeInline parts 0 mem).2 i.1)) := by
  have result := writeCursor_assemble (parts.map fun part => (true, part)) mem h
  rw [writeInline_cursor] at result
  simpa [Function.comp_def, List.map_const'] using result

end SszNative.Cursor
