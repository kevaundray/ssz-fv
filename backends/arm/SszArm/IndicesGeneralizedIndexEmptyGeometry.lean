import SszArm.IndicesGeneralizedIndexEmptyRun
import SszArm.CodecStack

namespace SszArm.Indices.GeneralizedIndex.Empty

open Delimited (Protected)

def stackSlot (s : ArmState) (displacement : Nat) : BitVec 64 :=
  r (.GPR 31#5) s - BitVec.ofNat 64 displacement

structure Owned (s : ArmState) : Prop where
  stackLow : 240 ≤ (r (.GPR 31#5) s).toNat
  outputBound : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  outputStack : Protected (SszArm.Codec.Stack.envelope (r (.GPR 31#5) s).toNat 240)
    (r (.GPR 0#5) s).toNat 68

theorem stackSlot_toNat (s : ArmState) (owned : Owned s)
    (displacement : Nat) (within : displacement ≤ 240) :
    (stackSlot s displacement).toNat = (r (.GPR 31#5) s).toNat - displacement :=
  SszArm.Codec.Stack.sub_toNat _ displacement (Nat.le_trans within owned.stackLow)

theorem add_toNat (address : BitVec 64) (offset : Nat)
    (bound : address.toNat + offset < 2^64) :
    (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
  have offsetBound : offset < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound,
    Nat.mod_eq_of_lt bound]

theorem output_toNat (s : ArmState) (owned : Owned s)
    (offset : Nat) (within : offset < 68) :
    (r (.GPR 0#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 0#5) s).toNat + offset :=
  add_toNat _ offset (by have bound := owned.outputBound; omega)

theorem stackSlot_bound (s : ArmState) (owned : Owned s)
    (displacement bytes : Nat) (within : displacement ≤ 240) (fits : bytes ≤ displacement) :
    (stackSlot s displacement).toNat + bytes ≤ 2^64 := by
  rw [stackSlot_toNat s owned displacement within]
  have original := (r (.GPR 31#5) s).isLt
  have low := owned.stackLow
  omega

theorem output_stack_apart (s : ArmState) (owned : Owned s) :
    (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 240 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat := by
  rcases owned.outputStack with empty | separate
  · omega
  · have apart := separate ((r (.GPR 31#5) s).toNat - 240, 240)
      (by simp [SszArm.Codec.Stack.envelope])
    have low := owned.stackLow
    dsimp at apart
    omega

theorem output_slot_apart (s : ArmState) (owned : Owned s)
    (offset bytes displacement slotBytes : Nat)
    (outputWithin : offset + bytes ≤ 68) (offsetWithin : offset < 68)
    (stackWithin : displacement ≤ 240) (slotWithin : slotBytes ≤ displacement) :
    (r (.GPR 0#5) s + BitVec.ofNat 64 offset).toNat + bytes ≤
      (stackSlot s displacement).toNat ∨
    (stackSlot s displacement).toNat + slotBytes ≤
      (r (.GPR 0#5) s + BitVec.ofNat 64 offset).toNat := by
  rw [output_toNat s owned offset offsetWithin, stackSlot_toNat s owned displacement stackWithin]
  have apart := output_stack_apart s owned
  have low := owned.stackLow
  omega

end SszArm.Indices.GeneralizedIndex.Empty
