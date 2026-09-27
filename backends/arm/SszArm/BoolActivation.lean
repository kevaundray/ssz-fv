import SszArm.BoolReturn
import SszArm.BoolBlockMemory

namespace SszArm.BoolCodec

/-- Byte equality suffices for architectural reads, including wrapping addresses. -/
theorem read_bytes_congr (s t : ArmState) (n : Nat) (address : BitVec 64)
    (h : ∀ i < n, read_mem (address + BitVec.ofNat 64 i) s =
      read_mem (address + BitVec.ofNat 64 i) t) :
    read_mem_bytes n address s = read_mem_bytes n address t := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih =>
    simp only [read_mem_bytes]
    have hh : read_mem address s = read_mem address t := by
      simpa using h 0 (by omega)
    have ht : read_mem_bytes n (address + 1#64) s =
        read_mem_bytes n (address + 1#64) t := by
      apply ih
      intro i hi
      have ha : address + 1#64 + BitVec.ofNat 64 i =
          address + BitVec.ofNat 64 (i + 1) := by
        simp only [BitVec.ofNat_add]
        bv_omega
      rw [ha]
      exact h (i + 1) (by omega)
    rw [hh, ht]

/-- The saved x19--x30 activation remains separate from output and lowering scratch. -/
def ActivationPreserved (initial current : ArmState) : Prop :=
  ∀ i < 96, read_mem (r (.GPR 31) initial + BitVec.ofNat 64 (272 + i)) current =
    read_mem (r (.GPR 31) initial + BitVec.ofNat 64 (272 + i)) initial

theorem activation_word (initial current : ArmState) (offset : Nat)
    (h : ActivationPreserved initial current) (hb : offset + 8 ≤ 96) :
    read_mem_bytes 8 (r (.GPR 31) initial + BitVec.ofNat 64 (272 + offset)) current =
      read_mem_bytes 8 (r (.GPR 31) initial + BitVec.ofNat 64 (272 + offset)) initial := by
  apply read_bytes_congr
  intro i hi
  simpa [BitVec.ofNat_add, BitVec.add_assoc, Nat.add_assoc] using h (offset + i) (by omega)

/-- The return instruction restores the original saved return address. -/
theorem returned_pc_of_activation (initial current : ArmState)
    (hsp : r (.GPR 31) current = r (.GPR 31) initial)
    (h : ActivationPreserved initial current) :
    read_pc (returned current) =
      read_mem_bytes 8 (r (.GPR 31) initial + 280#64) initial := by
  simp only [returned, state_simp_rules, hsp]
  exact activation_word initial current 8 h (by decide)

theorem activation_of_frame (initial current : ArmState)
    (hs : ScratchSeparated initial)
    (hout : (r (.GPR 0#5) initial).toNat + 80 ≤ (r (.GPR 31#5) initial).toNat + 272 ∨
      (r (.GPR 31#5) initial).toNat + 368 ≤ (r (.GPR 0#5) initial).toNat)
    (hframe : ∀ a : BitVec 64,
      (a.toNat < (r (.GPR 0#5) initial).toNat ∨
        (r (.GPR 0#5) initial).toNat + 76 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) initial).toNat - 32 ∨
        (r (.GPR 31#5) initial).toNat ≤ a.toNat) →
      current.mem a = initial.mem a) :
    ActivationPreserved initial current := by
  rcases hs with ⟨hlo, hhi, hospace, hsep⟩
  intro i hi
  apply hframe
  · bv_omega
  · bv_omega

end SszArm.BoolCodec
