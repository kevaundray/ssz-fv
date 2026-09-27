import SszArm.DelimitedMemory

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem Protected.subspan {writes : List Span} {address bytes : Nat}
    (owned : Protected writes address bytes) (offset width : Nat) (within : offset + width ≤ bytes) :
    Protected writes (address + offset) width := by
  by_cases empty : width = 0
  · exact Or.inl empty
  · right
    intro span member
    rcases owned with zero | separated
    · omega
    · have hsep := separated span member
      omega

theorem MemoryFrame.read {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (address : BitVec 64) (bytes : Nat)
    (physical : address.toNat + bytes ≤ 2^64) (owned : Protected writes address.toNat bytes) :
    read_mem_bytes bytes address t = read_mem_bytes bytes address s := by
  apply BitVec.eq_of_toNat_eq
  have equality := Option.some.inj (frame.load address.toNat bytes physical owned)
  simpa only [widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq] using equality

def OptionOwned (writes : List Span) (s : ArmState) (address : BitVec 64) : Option Nat → Prop
  | none => Protected writes address.toNat 24
  | some _ => Protected writes address.toNat 24 ∧
      NatOwned writes (read_mem_bytes 8 (address + 8#64) s)
        (read_mem_bytes 8 (address + 16#64) s)

/-- Borrowed option fields and its cap limbs survive writes by static ownership;
there is no disjointness requirement between the cap and the input bytes. -/
theorem option_preserved {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (address : BitVec 64) (limit : Option Nat)
    (physical : address.toNat + 24 ≤ 2^64)
    (input : SszNative.NatMemory.OptionAt (widthLoad s) address.toNat limit)
    (owned : OptionOwned writes s address limit) :
    SszNative.NatMemory.OptionAt (widthLoad t) address.toNat limit := by
  cases limit with
  | none =>
    have header : Protected writes address.toNat 24 := owned
    change widthLoad t address.toNat 4 = some 0
    rw [frame.load _ _ (by omega) (by simpa using header.subspan 0 4 (by decide))]
    exact input
  | some limit =>
    have pointer : widthLoad s (address.toNat + 8) 8 =
        some (read_mem_bytes 8 (address + 8#64) s).toNat := by
      simp [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    have payload : widthLoad s (address.toNat + 8 + 8) 8 =
        some (read_mem_bytes 8 (address + 16#64) s).toNat := by
      simp [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_assoc]
    obtain ⟨tag, pair⟩ :=
      (SszNative.NatMemory.option_some_iff_pair _ _ _ _ _ pointer payload).mp input
    rcases owned with ⟨header, limbs⟩
    refine ⟨?_, SszNative.NatMemory.Pair.at _ _ _ _ _
      (frame.pair _ _ limit pair limbs) ?_ ?_⟩
    · rw [frame.load _ _ (by omega) (by simpa using header.subspan 0 4 (by decide))]
      exact tag
    · exact (frame.load _ _ (by omega) (header.subspan 8 8 (by decide))).trans pointer
    · have read := frame.load (address.toNat + 16) 8 (by omega)
        (header.subspan 16 8 (by decide))
      simpa only [Nat.add_assoc] using
        read.trans (by simpa only [Nat.add_assoc] using payload)

end SszArm.Delimited
