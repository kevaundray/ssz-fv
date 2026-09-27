import SszX86.NatDivisionLoopStep

namespace SszX86.NatDivision.Loop
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every physical word is retained, including redundant high zero words. -/
def WordsAt (m : DataMem) (p : BitVec 64) (words : List (BitVec 64)) : Prop :=
  ∀ i (hi : i < words.length), Mem.loadInt m (p + BitVec.ofNat 64 (8*i)) 8 =
    some (words[i].toNat : Int)

/-- Byte-exact footprint of the entire reverse pass. -/
def Frame (m n : DataMem) (p sp : BitVec 64) (count : Nat) : Prop :=
  ∀ a, (∀ i < 8*count, a ≠ p + BitVec.ofNat 64 i) →
    (∀ i < 8, a ≠ sp - 8#64 + BitVec.ofNat 64 i) → n.get? a = m.get? a

theorem word_apart (p : BitVec 64) (count i j : Nat)
    (bound : p.toNat + 8*count ≤ 2^64) (hi : i < count) (hj : j < count) (hne : i ≠ j) :
    ∀ a < 8, ∀ b < 8,
      p + BitVec.ofNat 64 (8*i) + BitVec.ofNat 64 a ≠
        p + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 b := by
  intro a ha b hb equal
  simp only [memmove_addr_add] at equal
  have h := memmove_addr_injective p (8*count) (8*i+a) (8*j+b)
    bound (by omega) (by omega) equal
  omega

theorem load_word_store (m : DataMem) (p value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 value.toInt) p 8 = some (value.toNat : Int) := by
  rw [BoolCodec.load_store_same _ _ 8 _ (by decide)]
  congr 1
  have cast := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at cast
  simp only [Int.take]
  omega

theorem iteration_frame (s t : MachineData) (ra limb : BitVec 64)
    (h : Iteration s ra limb t) (p : BitVec 64) (n : Nat)
    (dest : get s .r14 = p) (index : get s .rbp = BitVec.ofNat 64 (8*n)) :
    Frame s.dmem t.dmem p (get s .rsp) (n+1) := by
  intro a outside slot
  rw [h.memory, dest, index]
  rw [BoolCodec.store_frame _ p a (8*(n+1)) (8*n) 8 _ (by omega) outside]
  apply memmove_store_lookup_outside
  intro i hi
  exact slot i (by simpa only [Int.toBytes_length] using hi)

theorem frame_trans (m n k : DataMem) (p sp : BitVec 64) (a b : Nat)
    (ha : a ≤ b) (first : Frame m n p sp b) (second : Frame n k p sp a) :
    Frame m k p sp b := by
  intro address outside slot
  rw [second address (fun i hi => outside i (by omega)) slot, first address outside slot]

/-- A frame protects arbitrary caller-owned loads, not only named spill slots. -/
theorem frame_load (m n : DataMem) (p sp address : BitVec 64) (count byteCount : Nat)
    (frame : Frame m n p sp count)
    (words : ∀ i < byteCount, ∀ j < 8*count,
      address + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j)
    (slot : ∀ i < byteCount, ∀ j < 8,
      address + BitVec.ofNat 64 i ≠ sp - 8#64 + BitVec.ofNat 64 j) :
    Mem.loadInt n address byteCount = Mem.loadInt m address byteCount := by
  apply memmove_loadInt_congr
  intro i hi
  exact frame _ (words i hi) (slot i hi)

end SszX86.NatDivision.Loop
