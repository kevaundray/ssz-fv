import SszX86.EmitUintModel
import SszX86.EmitBitsFinishMemory

namespace SszX86.Emit.Uint
open BoolCodec UintCodec

/-- Reuse the existing byte-exact native copy invariant as an output-prefix
invariant. No source buffer, initialized output, or extra allocation is assumed. -/
abbrev Prefix (original current : DataMem) (out : BitVec 64) (bytes : Ssz.Bytes)
    (written : Nat) : Prop := MoveInv current original out bytes.toList 0 written

theorem prefix_empty (m : DataMem) (out : BitVec 64) (bytes : Ssz.Bytes) :
    Prefix m m out bytes 0 := by
  refine ⟨Nat.le_refl _, Nat.zero_le _, ?_, ?_⟩
  · intro i lo hi
    omega
  · intro a outside
    rfl

theorem prefix_frame {original current : DataMem} {out : BitVec 64} {bytes : Ssz.Bytes}
    {written : Nat} (hprefix : Prefix original current out bytes written) :
    MemoryFrame original current (fun a => InSpan a out written) := by
  intro a outside
  apply hprefix.frame
  intro i lo hi equal
  exact outside ⟨i, hi, equal⟩

theorem prefix_mapped {original current : DataMem} {out : BitVec 64} {bytes : Ssz.Bytes}
    {written : Nat} (hprefix : Prefix original current out bytes written)
    (hmap : Large.Mapped original out bytes.size) (physical : bytes.size ≤ 2 ^ 64) :
    Large.Mapped current out bytes.size := by
  intro i hi
  by_cases before : i < written
  · refine ⟨bytes[i], ?_⟩
    simpa only [Array.getElem?_toList, Array.getElem?_eq_getElem hi] using
      hprefix.copied i (Nat.zero_le _) before
  · obtain ⟨byte, read⟩ := hmap i hi
    refine ⟨byte, ?_⟩
    rw [hprefix.frame]
    · exact read
    · intro j lo hj equal
      have size : written ≤ bytes.size := by
        simpa only [Array.length_toList] using hprefix.bounded
      have inj : i = j := by
        have same := congrArg BitVec.toNat ((BitVec.add_right_inj out).mp equal)
        simp only [BitVec.toNat_ofNat] at same
        have ib : i < 2 ^ 64 := by omega
        have jb : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt jb] at same
        exact same
      omega

/-- One real byte store extends the prefix and leaves every other address
exactly as it was, including unreadable original output-tail bytes. -/
theorem prefix_store {original current : DataMem} {out : BitVec 64} {bytes : Ssz.Bytes}
    {written : Nat} (hprefix : Prefix original current out bytes written)
    (physical : out.toNat + bytes.size ≤ 2 ^ 64) (within : written < bytes.size) :
    Prefix original
      (Mem.storeInt current (out + BitVec.ofNat 64 written) 1 bytes[written].toBitVec.toInt)
      out bytes (written + 1) := by
  rw [Mem.storeInt, Bits.byte_encoding]
  refine ⟨Nat.zero_le _, by simpa only [Array.length_toList] using (by omega : written + 1 ≤ bytes.size), ?_, ?_⟩
  · intro i lo hi
    by_cases last : i = written
    · subst i
      have read := memmove_store_lookup_inside current (out + BitVec.ofNat 64 written)
        [bytes[written]] 0 (by change 0 < 1; decide) (by change 1 ≤ 2 ^ 64; decide)
      simpa only [BitVec.add_zero, List.getElem?_cons_zero,
        Array.getElem?_toList, Array.getElem?_eq_getElem within] using read
    · rw [memmove_store_lookup_outside]
      · exact hprefix.copied i lo (by omega)
      · intro j hj equal
        have zero : j = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
        subst j
        simp only [BitVec.add_zero] at equal
        exact last (memmove_addr_injective out bytes.size i written physical
          (by omega) within equal)
  · intro a outside
    rw [memmove_store_lookup_outside]
    · apply hprefix.frame
      intro i lo hi
      exact outside i lo (by omega)
    · intro j hj equal
      have zero : j = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
      subst j
      simp only [BitVec.add_zero] at equal
      exact outside written (Nat.zero_le _) (by omega) equal

theorem prefix_output {original current : DataMem} {out : BitVec 64} {bytes : Ssz.Bytes}
    (hprefix : Prefix original current out bytes bytes.size) : BytesAt current out bytes := by
  intro i hi
  simpa only [Array.getElem?_toList, Array.getElem?_eq_getElem hi] using
    hprefix.copied i (Nat.zero_le _) hi

/-- Width and number allocations remain their original padded representations;
separation is required only from actual output writes, not from other reads. -/
theorem prefix_protected {original current : DataMem} {out : BitVec 64} {bytes : Ssz.Bytes}
    {written : Nat} (hprefix : Prefix original current out bytes written)
    (p : BitVec 64) (byteCount : Nat)
    (readGuard : ∀ a, InSpan a p byteCount → ¬ InSpan a out bytes.size) :
    Mem.loadInt current p byteCount = Mem.loadInt original p byteCount := by
  apply Bits.protected_load (prefix_frame hprefix)
  intro a inside output
  obtain ⟨i, hi, equal⟩ := output
  have bound : written ≤ bytes.size := by
    simpa only [Array.length_toList] using hprefix.bounded
  exact readGuard a inside ⟨i, by omega, equal⟩

end SszX86.Emit.Uint
