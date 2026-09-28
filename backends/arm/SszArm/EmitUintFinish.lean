import SszArm.EmitUintByteExec
import SszArm.EmitUintFrame

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (Protected)

@[irreducible] def resultFinish (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) : ArmState :=
  w .PC (base + 1004#64) (write_mem_bytes 8 args.result (BitVec.ofNat 64 size) s)

theorem result_finish (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : NatOperand) (size : Nat)
    (code : CodeAt s base) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1000#64)
    (length : r (.GPR 1#5) s = BitVec.ofNat 64 size)
    (bytes : SszNative.ByteView.BytesAt (widthLoad s) args.output.toNat
      (SszNative.Serialize.emit (.uint width) (.uint number))) :
    run 1 s = resultFinish s base args size ∧
    Produced s (resultFinish s base args size) args (.uint width) (.uint number) size base := by
  have resultBound : args.result.toNat + 8 ≤ 2^64 := by have := owned.resultBound; omega
  have outputBound : args.output.toNat + size ≤ 2^64 := by
    have := owned.outputBound
    have := owned.fitting
    omega
  have emittedSize : (SszNative.Serialize.emit (.uint width) (.uint number)).size = size := by
    simp [SszNative.Serialize.emit, SszNative.Limbs.bytes, expected_width owned]
  have storeFrame := Delimited.store_frame s args.result 8 (BitVec.ofNat 64 size) resultBound
  have outputProtected : Protected [(args.result.toNat, 8)] args.output.toNat size := by
    by_cases empty : size = 0
    · exact Or.inl empty
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rcases owned.outputResult with zero | separated
      · have := owned.fitting; omega
      · have apart := separated (args.result.toNat, 8) (by simp)
        have := owned.fitting
        change args.output.toNat + size ≤ args.result.toNat ∨
          args.result.toNat + 8 ≤ args.output.toNat
        change args.output.toNat + args.capacity.toNat ≤ args.result.toNat ∨
          args.result.toNat + 8 ≤ args.output.toNat at apart
        omega
  have storedBytes := storeFrame.bytes args.output
    (SszNative.Serialize.emit (.uint width) (.uint number))
    (by simpa only [emittedSize] using outputBound)
    (by simpa only [emittedSize] using outputProtected) bytes
  constructor
  · change stepi s = _
    rw [byte_step s base .p1000 code pc error aligned]
    change r .PC s = base + 1000#64 at pc
    simp [resultFinish, ByteOp.effect, next, Dispatch.next, state_simp_rules,
      pc, registers.result, length, BitVec.add_assoc]
  · constructor
    · simp [resultFinish, state_simp_rules]
    · simp [resultFinish, state_simp_rules]
    · simpa [resultFinish, state_simp_rules] using error
    · simpa [resultFinish, state_simp_rules] using registers.result
    · simpa [resultFinish, state_simp_rules] using registers.stack
    · simp only [resultFinish, state_simp_rules]
      exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ resultBound
    · have loads : widthLoad (resultFinish s base args size) =
          widthLoad (write_mem_bytes 8 args.result (BitVec.ofNat 64 size) s) :=
        load_eq_of_mem_eq (by simp [resultFinish, state_simp_rules])
      rw [loads]
      exact storedBytes
    · intro address outside
      have resultOutside := outside (args.result.toNat, 8) (by simp [bodyWrites])
      simp only [resultFinish, state_simp_rules]
      exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address resultBound resultOutside
    · intro reg member
      simp [resultFinish, state_simp_rules]
    · intro reg low high
      simp [resultFinish, state_simp_rules]

theorem prepend_produced {s u t : ArmState} {base : BitVec 64} {args : Args}
    {width number : NatOperand} {size : Nat} (frame : Frame s u args size)
    (produced : Produced u t args (.uint width) (.uint number) size base) :
    Produced s t args (.uint width) (.uint number) size base := by
  refine { produced with
    program := produced.program.trans frame.program
    frame := ?_
    registers := ?_
    vectors := ?_ }
  · intro address outside
    exact (produced.frame address outside).trans (frame.memory address outside)
  · intro reg member
    have outside : reg ∉ [1#5, 8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 14#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    exact (produced.registers reg member).trans (frame.registers reg outside)
  · intro reg low high
    exact (produced.vectors reg low high).trans (congrArg (BitVec.setWidth 64) (frame.vectors reg))

end SszArm.Emit.Uint
