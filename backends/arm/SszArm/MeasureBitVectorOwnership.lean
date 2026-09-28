import SszArm.MeasureBitVectorCapReady
import SszArm.MeasureBitVectorHeader
import SszArm.MeasureBitVectorCompare
import SszArm.MeasureScalarTransition

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Packed)
open UintCodec (widthLoad)

theorem cap_reads {s : ArmState} {args : Args} {cap : NatOperand} {bits : Packed}
    (owned : Owned s args (.bitVector cap) (.bits bits)) :
    read_mem_bytes 8 (args.descriptor + 8#64) s = cap.pointer ∧
      read_mem_bytes 8 (args.descriptor + 16#64) s = cap.payload := by
  have fields : SszNative.NatArithmetic.operandAt (widthLoad s) (args.descriptor.toNat + 8) cap :=
    owned.descriptor.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    have value := Option.some.inj fields.1
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using value
  · apply BitVec.eq_of_toNat_eq
    have value := Option.some.inj fields.2.1
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_assoc] using value

theorem count_reads {s : ArmState} {args : Args} {cap : NatOperand} {bits : Packed}
    (owned : Owned s args (.bitVector cap) (.bits bits)) :
    read_mem_bytes 8 (args.value + 32#64) s = bits.count.setWidth 64 ∧
      read_mem_bytes 8 (args.value + 40#64) s = (bits.count >>> 64).setWidth 64 :=
  owned.value_at.2.2.2.2

theorem length_read {s : ArmState} {args : Args} {cap : NatOperand} {bits : Packed}
    (owned : Owned s args (.bitVector cap) (.bits bits)) :
    read_mem_bytes 8 (args.value + 24#64) s = BitVec.ofNat 64 bits.bytes.size := by
  apply BitVec.eq_of_toNat_eq
  have physical : bits.bytes.size < 2^64 := owned.physical
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using owned.value_at.2.1

theorem CapFrame.stack_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (frame : CapFrame s t) (owned : Owned s args desc value)
    (stack : r (.GPR 31#5) s = args.bodySP) :
    Delimited.MemoryFrame (bodyStackWrites args (outcome s args desc value)) s t := by
  have low := owned.stackLow
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]
    bv_omega
  exact frame.memoryFrame _ (by simp [position, bodyStackWrites])
    (by rw [stack, Args.bodySP]; bv_omega)

theorem CapFrame.local_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (frame : CapFrame s t) (owned : Owned s args desc value)
    (stack : r (.GPR 31#5) s = args.bodySP) :
    Delimited.MemoryFrame (localWrites args (outcome s args desc value)) s t := by
  apply (frame.stack_frame owned stack).weaken
  intro span member
  simp only [localWrites, stackWrites, List.mem_append]
  exact Or.inl (Or.inr member)

theorem CapFrame.owned {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (frame : CapFrame s t) (owned : Owned s args desc value)
    (stack : r (.GPR 31#5) s = args.bodySP) : Owned t args desc value :=
  owned.of_local_frame (frame.local_frame owned stack)

theorem CapFrame.prepend {s u t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (frame : CapFrame s u) (owned : Owned s args desc value)
    (stack : r (.GPR 31#5) s = args.bodySP) (post : Produced u t args desc value base) :
    Produced s t args desc value base := by
  apply post.prepend_stack owned (frame.stack_frame owned stack) frame.program
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact frame.registers _ (by decide)
  · intro reg low high
    rw [frame.vectors]

theorem compared_cap_frame (s : ArmState) (base : BitVec 64)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) : CapFrame s (compared s base) :=
  CapFrame.of_scan (compared_frame s base safe) (compared_register s base 9#5)

end SszArm.Measure.BitVector
