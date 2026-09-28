import SszArm.EmitUintLoopStore

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected)

def byteStoreWrites (s : ArmState) (kind : ByteStoreKind) : List Delimited.Span :=
  [((r (.GPR 31#5) s - 16#64).toNat, 8), ((byteStoreAddress s kind).toNat, 1)]

theorem byteStored_exact_frame {s : ArmState} {args : Args} {width number : NatOperand} {size index : Nat}
    (base : BitVec 64) (kind : ByteStoreKind) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (current : (r (.GPR kind.index) s).toNat = index)
    (inside : index < size) : MemoryFrame (byteStoreWrites s kind) s (byteStored s base kind) := by
  have position := byteStore_position kind owned registers current inside
  have stack := body_stack_safe owned registers
  have bound := owned.outputBound
  have fitting := owned.fitting
  intro address outside
  have outsideStack := outside ((r (.GPR 31#5) s - 16#64).toNat, 8) (by simp [byteStoreWrites])
  have outsideOutput := outside ((byteStoreAddress s kind).toNat, 1) (by simp [byteStoreWrites])
  simp only [Prod.fst, Prod.snd] at outsideStack outsideOutput
  simp only [byteStored, ArmState.mem_w_eq_mem, byteStoreMemory, NatCompare.saved]
  rw [BoolCodec.write_mem_bytes_frame _ _ 1 _ address (by rw [position]; omega) outsideOutput]
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ address (by bv_omega) outsideStack

theorem byteStored_frame {s : ArmState} {args : Args} {width number : NatOperand} {size index : Nat}
    (base : BitVec 64) (kind : ByteStoreKind) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (current : (r (.GPR kind.index) s).toNat = index)
    (inside : index < size) : Frame s (byteStored s base kind) args size := by
  refine ⟨byteStored_program _ _ _, byteStored_error _ _ _,
    fun reg _ => byteStored_register _ _ _ reg, byteStored_vector _ _ _, ?_⟩
  have exactFrame := byteStored_exact_frame base kind owned registers current inside
  have position := byteStore_position kind owned registers current inside
  have low := owned.stackLow
  have slot : (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
    rw [registers.stack]
    unfold Args.bodySP
    bv_omega
  intro address outside
  apply exactFrame
  intro span member
  simp only [byteStoreWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have apart := outside (args.stack.toNat - 176, 16) (by simp [bodyWrites])
    simp only [Prod.fst, Prod.snd] at apart ⊢
    rw [slot]
    omega
  · have positive : size ≠ 0 := by omega
    have apart := outside (args.output.toNat, size) (by simp [bodyWrites, positive])
    simp only [Prod.fst, Prod.snd] at apart ⊢
    rw [position]
    omega

theorem byteStored_byte {s : ArmState} {args : Args} {width number : NatOperand} {size index : Nat}
    (base : BitVec 64) (kind : ByteStoreKind) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (current : (r (.GPR kind.index) s).toNat = index)
    (inside : index < size) :
    widthLoad (byteStored s base kind) (args.output.toNat + index) 1 =
      some ((r (.GPR 12#5) s).setWidth 8).toNat := by
  have position := byteStore_position kind owned registers current inside
  have address : BitVec.ofNat 64 (args.output.toNat + index) = byteStoreAddress s kind := by
    rw [← position, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bound := owned.outputBound
  have fitting := owned.fitting
  simp only [widthLoad, byteStored, read_mem_bytes_of_w, address, byteStoreMemory]
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 1 _ _ (by rw [position]; omega)]

theorem byteStored_prior {s : ArmState} {args : Args} {width number : NatOperand} {size index : Nat}
    (base : BitVec 64) (kind : ByteStoreKind) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (current : (r (.GPR kind.index) s).toNat = index)
    (inside : index < size) (prior : Nat) (earlier : prior < index) :
    widthLoad (byteStored s base kind) (args.output.toNat + prior) 1 =
      widthLoad s (args.output.toNat + prior) 1 := by
  have position := byteStore_position kind owned registers current inside
  have low := owned.stackLow
  have slot : (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
    rw [registers.stack]
    unfold Args.bodySP
    bv_omega
  have bound := owned.outputBound
  have fitting := owned.fitting
  apply (byteStored_exact_frame base kind owned registers current inside).load _ 1 (by omega)
  right
  intro span member
  simp only [byteStoreWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp only [Prod.fst, Prod.snd]
    rw [slot]
    rcases owned.outputStack with empty | separate
    · omega
    · have apart := separate (args.stack.toNat - 176, 16) (by simp [stackWrites])
      simp only [Prod.fst, Prod.snd] at apart
      omega
  · simp only [Prod.fst, Prod.snd]
    rw [position]
    exact Or.inl (by omega)

end SszArm.Emit.Uint
