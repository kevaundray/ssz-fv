import SszArm.NatMulReserveCommit

namespace SszArm.NatMul

private theorem read_zero_bytes (s : ArmState) (n : Nat) (address : BitVec 64)
    (zero : ∀ i < n, read_mem (address + BitVec.ofNat 64 i) s = 0#8) :
    read_mem_bytes n address s = 0 := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih =>
    have first : read_mem address s = 0#8 := by simpa using zero 0 (by omega)
    have rest : read_mem_bytes n (address + 1#64) s = 0 := by
      apply ih
      intro i hi
      have eq : address + 1#64 + BitVec.ofNat 64 i =
          address + BitVec.ofNat 64 (i + 1) := by
        simp only [BitVec.ofNat_add]
        bv_omega
      rw [eq]
      exact zero (i + 1) (by omega)
    simp [read_mem_bytes, first, rest]

/-- Byte initialization proves every actual eight-byte load; this is not an
assumption on the future destination contents. -/
theorem zero_bytes_words (s : ArmState) (pointer : BitVec 64) (words : Nat)
    (physical : pointer.toNat + 8 * words ≤ 2^64)
    (zero : ∀ a : BitVec 64, pointer.toNat ≤ a.toNat →
      a.toNat < pointer.toNat + 8 * words → s.mem a = 0#8) :
    UintCodec.WidthWords s pointer (List.replicate words 0#64) := by
  intro i
  have index : i.val < words := by simpa using i.isLt
  have word : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * i.val)) s = 0#64 := by
    apply read_zero_bytes
    intro j hj
    change s.mem _ = 0#8
    apply zero <;> bv_omega
  simpa using word

theorem ReserveZeroState.words {s t : ArmState} {base : BitVec 64}
    (post : ReserveZeroState s t base) (words : Nat)
    (count : (r (.GPR 2#5) s).toNat = 8 * words)
    (physical : (r (.GPR 20#5) t).toNat + 8 * words ≤ 2^64) :
    UintCodec.WidthWords t (r (.GPR 20#5) t) (List.replicate words 0#64) := by
  apply zero_bytes_words t _ words physical
  intro a low high
  exact post.zero_bytes a ⟨low, by rw [count]; exact high⟩

theorem ReserveZeroState.cursor {s t : ArmState} {base : BitVec 64}
    (post : ReserveZeroState s t base)
    (physical : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64)
    (separate : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ (r (.GPR 20#5) t).toNat ∨
      (r (.GPR 20#5) t).toNat + (r (.GPR 2#5) s).toNat ≤ (r (.GPR 5#5) s + 16#64).toNat) :
    read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = r (.GPR 12#5) s := by
  have same : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t =
      read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) (reserveCursorMemory s) := by
    apply BoolCodec.read_bytes_congr
    intro i hi
    change t.mem _ = (reserveCursorMemory s).mem _
    rw [post.memory, Memset.image, if_neg]
    rw [post.pointer] at separate
    bv_omega
  exact same.trans (BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ physical)

end SszArm.NatMul
