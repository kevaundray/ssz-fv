import SszIndicesTypes
import SszSerializeMeasure

set_option autoImplicit false

namespace SszNative.Indices

/-- Zero-extended observation of the supplied representation; no normalization. -/
def word (index : NatOperand) (position : Nat) : BitVec 64 :=
  match index with
  | .small value => if position = 0 then value else 0
  | .large _ words => words[position]?.getD 0

theorem word_eq (index : NatOperand) (position : Nat) :
    word index position = index.words[position]?.getD 0 := by
  cases index with
  | small value => cases position <;> simp [word, NatOperand.words]
  | large pointer words => rfl

/-- Highest significant limb scan, including empty and zero-padded Large inputs. -/
def bitLength (index : NatOperand) : Nat :=
  let count := index.wordCount
  if count = 0 then 0 else
    64 * (count - 1) + (word index (count - 1)).toNat.log2 + 1

def depth (index : NatOperand) : Nat := bitLength index - 1

def checkedDepth (index : NatOperand) : Except Error Nat :=
  if index.wordCount = 0 then .error (.notAGindex index) else .ok (depth index)

def length (index : NatOperand) : Except Error Nat := do
  let result ← checkedDepth index
  if result = 0 then .error .rootHasNoBranch else .ok result

def bit (index : NatOperand) (position : Nat) : Bool :=
  if position / 64 < 2 ^ 64 then
    ((word index (position / 64) >>> (position % 64)) &&& 1) != 0
  else false

def wordCount (bits : Nat) : Except Error Nat :=
  let count := bits / 64 + if bits % 64 = 0 then 0 else 1
  if count < 2 ^ 64 then .ok count else .error scratch

def lowMask (bits : Nat) : BitVec 64 :=
  if bits = 64 then -1 else (1 <<< bits) - 1

def rangeWord (position start stop : Nat) : BitVec 64 :=
  lowMask (min (stop - position * 64) 64) &&&
    ~~~(lowMask (min (start - position * 64) 64))

def shiftedWord (index : NatOperand) (shift position : Nat) : BitVec 64 :=
  let offset := shift / 64 + position
  if shift / 64 < 2 ^ 64 ∧ offset < 2 ^ 64 then
    let bits := shift % 64
    let low := word index offset >>> bits
    if bits = 0 then low else
      low ||| ((if offset + 1 < 2 ^ 64 then word index (offset + 1) else 0) <<< (64 - bits))
  else 0

/-- Descending short-circuit scan, without constructing temporary limb arrays. -/
def allWords (predicate : Nat → Bool) : Nat → Bool
  | 0 => true
  | count + 1 => predicate count && allWords predicate count

/-- Its numeric xor interpretation requires the flipped prefix to be non-root.
The source deliberately compares widths before applying xor. -/
def prefixEqual (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat) : Bool :=
  let bits := bitLength left - leftShift
  if bits != bitLength right - rightShift then false else
    let count := (bits / 64 + if bits % 64 = 0 then 0 else 1) % 2 ^ 64
    allWords (fun i =>
      (shiftedWord left leftShift i ^^^ (if flip && i == 0 then 1 else 0)) ==
        shiftedWord right rightShift i) count

def PrefixFlipDomain (left : NatOperand) (shift : Nat) (flip : Bool) : Prop :=
  flip = true → 1 < bitLength left - shift

theorem wordCount_zero_iff (index : NatOperand) :
    index.wordCount = 0 ↔ index.value = 0 := by
  constructor
  · intro zero
    have selected := Serialize.significant_prefix_value index.words index.words.length
    rw [List.take_length] at selected
    change Limbs.value (index.words.take index.wordCount) = index.value at selected
    simpa [zero, Limbs.value] using selected.symm
  · intro zero
    by_cases count : index.wordCount = 0
    · exact count
    · have positive : 0 < index.wordCount := Nat.pos_of_ne_zero count
      have measured := Serialize.bitLength_significant index.words positive
      change Serialize.bitLength index.value = _ at measured
      simp only [zero, Serialize.bitLength, ↓reduceIte] at measured
      omega

theorem bitLength_value (index : NatOperand) :
    bitLength index = Serialize.bitLength index.value := by
  unfold bitLength
  dsimp only
  split
  · rename_i zero
    rw [(wordCount_zero_iff index).mp zero]
    rfl
  · rename_i nonzero
    rw [word_eq]
    exact (Serialize.bitLength_significant index.words (Nat.pos_of_ne_zero nonzero)).symm

theorem depth_value (index : NatOperand) : depth index = index.value.log2 := by
  rw [depth, bitLength_value]
  unfold Serialize.bitLength
  split
  · rename_i zero
    simp [zero]
  · omega

theorem checkedDepth_erase (index : NatOperand) :
    eraseResult (checkedDepth index) = .ok (Ssz.gindexDepth index.value) := by
  by_cases zero : index.value = 0
  · have count := (wordCount_zero_iff index).mpr zero
    simp [checkedDepth, count, eraseResult, Ssz.gindexDepth, zero]
  · have count : index.wordCount ≠ 0 := fun h => zero ((wordCount_zero_iff index).mp h)
    have positive : ¬ index.value < 1 := by omega
    simp [checkedDepth, count, eraseResult, Ssz.gindexDepth, positive, depth_value]

theorem length_erase (index : NatOperand) :
    eraseResult (length index) = .ok (Ssz.gindexLength index.value) := by
  by_cases zero : index.value = 0
  · have count := (wordCount_zero_iff index).mpr zero
    simp [length, checkedDepth, count, eraseResult, Ssz.gindexLength, Ssz.gindexDepth, zero,
      Bind.bind, Except.bind]
  · have count : index.wordCount ≠ 0 := fun h => zero ((wordCount_zero_iff index).mp h)
    have positive : ¬ index.value < 1 := by omega
    by_cases root : index.value.log2 = 0 <;>
      simp [length, checkedDepth, count, depth_value, root, eraseResult,
        Ssz.gindexLength, Ssz.gindexDepth, positive, Bind.bind, Except.bind]

theorem allWords_iff (predicate : Nat → Bool) (count : Nat) :
    allWords predicate count = true ↔ ∀ i, i < count → predicate i = true := by
  induction count with
  | zero => simp [allWords]
  | succ count ih =>
    simp only [allWords, Bool.and_eq_true, ih]
    constructor
    · intro ⟨last, earlier⟩ i bound
      by_cases equal : i = count
      · simpa [equal] using last
      · exact earlier i (by omega)
    · intro every
      exact ⟨every count (by omega), fun i bound => every i (by omega)⟩

end SszNative.Indices
