import SszArm.EmitUintLoopSmall
import SszArm.NatAddLoadState

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

/-- The eight actual save/index/load/restore instructions, followed by the real
backward branch into the common Large-byte shift block. -/
def largeReadOps : List ByteOp :=
  [.p1144, .p1148, .p1152, .p1156, .p1160, .p1164, .p1168, .p1172, .p1176]

@[irreducible] def largeWordLoaded (s : ArmState) (base : BitVec 64) (word : BitVec 64) : ArmState :=
  w .PC (base + 1076#64) (w (.GPR 12#5) word (NatCompare.saved s 10#5))

theorem large_word_run {s : ArmState} {args : Args} {width : NatOperand}
    {pointer : BitVec 64} {words : List (BitVec 64)} {size index : Nat}
    (base : BitVec 64) (owned : Owned s args (.uint width) (.uint (.large pointer words)) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1144#64)
    (pointerReg : r (.GPR 9#5) s = pointer)
    (indexReg : r (.GPR 12#5) s = BitVec.ofNat 64 (index / 8))
    (inside : index / 8 < words.length) :
    run 9 s = largeWordLoaded s base (words[index / 8]?.getD 0) := by
  have position : r .PC s = base + 1144#64 := pc
  have follows : ByteFollows base largeReadOps s := by
    simp [largeReadOps, ByteFollows, ByteOp.row, ByteOp.effect, put, next, Dispatch.next,
      state_simp_rules, position, BitVec.add_assoc]
  have stack := body_stack_safe owned registers
  have source := operand_source owned registers pointer words (by simp)
  have wordMemory := operand_words owned pointer words (by simp)
  have savedWords := (NatCompare.saved_frame s 10#5 stack).words pointer words source wordMemory
  have address : r (.GPR 9#5) s + (r (.GPR 12#5) s <<< 3) =
      pointer + BitVec.ofNat 64 (8 * (index / 8)) := by rw [pointerReg, indexReg]; bv_omega
  have loaded : read_mem_bytes 8 (r (.GPR 9#5) s + (r (.GPR 12#5) s <<< 3))
      (NatCompare.saved s 10#5) = words[index / 8]?.getD 0 := by
    rw [address]
    simpa only [List.getElem?_eq_getElem inside, Option.getD_some, Fin.getElem_fin] using
      savedWords ⟨index / 8, inside⟩
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 10#5) =
      r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  rw [show 9 = largeReadOps.length by rfl, byte_run base largeReadOps s code error aligned follows]
  have sequence : byteBlock base largeReadOps s =
      ByteOp.p1176.effect base (NatAdd.indexedReadSequence s 9#5 12#5 10#5 12#5) := by rfl
  rw [sequence, NatAdd.indexedReadSequence_eq s 9#5 12#5 10#5 12#5 _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) loaded restored]
  simp only [ByteOp.effect, largeWordLoaded, state_simp_rules]

@[simp] theorem largeWordLoaded_register (s : ArmState) (base word : BitVec 64) (reg : BitVec 5)
    (different : reg ≠ 12#5) :
    r (.GPR reg) (largeWordLoaded s base word) = r (.GPR reg) s := by
  simp [largeWordLoaded, NatCompare.saved, state_simp_rules, different]

@[simp] theorem largeWordLoaded_word (s : ArmState) (base word : BitVec 64) :
    r (.GPR 12#5) (largeWordLoaded s base word) = word := by
  simp [largeWordLoaded, NatCompare.saved, state_simp_rules]

@[simp] theorem largeWordLoaded_pc (s : ArmState) (base word : BitVec 64) :
    read_pc (largeWordLoaded s base word) = base + 1076#64 := by simp [largeWordLoaded, state_simp_rules]

theorem largeWordLoaded_frame {s : ArmState} {args : Args} {width number : NatOperand} {size : Nat}
    (base word : BitVec 64) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) : Frame s (largeWordLoaded s base word) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [largeWordLoaded, NatCompare.saved, state_simp_rules]
  · simp [largeWordLoaded, NatCompare.saved, state_simp_rules]
  · intro reg outside
    exact largeWordLoaded_register s base word reg (by simp_all)
  · intro reg
    simp [largeWordLoaded, NatCompare.saved, state_simp_rules]
  · intro address outside
    have apart := outside (args.stack.toNat - 176, 16) (by simp [bodyWrites])
    have low := owned.stackLow
    simp only [largeWordLoaded, ArmState.mem_w_eq_mem, NatCompare.saved]
    apply BoolCodec.write_mem_bytes_frame s _ 8 _ address
    · rw [registers.stack]
      unfold Args.bodySP
      bv_omega
    · rw [registers.stack]
      unfold Args.bodySP
      bv_omega

theorem largeWordLoaded_prefix {s : ArmState} {args : Args} {width number : NatOperand} {size count : Nat}
    (base word : BitVec 64) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (within : count ≤ size)
    (writtenPrefix : Prefix s args number count) : Prefix (largeWordLoaded s base word) args number count := by
  intro index inside
  have bound := owned.outputBound
  have fitting := owned.fitting
  have low := owned.stackLow
  have slot : (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
    rw [registers.stack]
    unfold Args.bodySP
    bv_omega
  have separate : Delimited.Protected [((r (.GPR 31#5) s - 16#64).toNat, 8)]
      (args.output.toNat + index) 1 := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    rw [slot]
    rcases owned.outputStack with empty | apart
    · omega
    · have separated := apart (args.stack.toNat - 176, 16) (by simp [stackWrites])
      omega
  have stored := Delimited.store_frame s (r (.GPR 31#5) s - 16#64) 8 (r (.GPR 10#5) s)
    (by rw [slot]; omega)
  have memory : (largeWordLoaded s base word).mem =
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 10#5) s) s).mem := by
    simp only [largeWordLoaded, ArmState.mem_w_eq_mem, NatCompare.saved]
  rw [load_eq_of_mem_eq memory]
  rw [stored.load _ 1 (by omega) separate]
  exact writtenPrefix index inside

end SszArm.Emit.Uint
