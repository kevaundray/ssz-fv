import SszArm.EmitBitsStore
import SszArm.EmitBitsWork

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

inductive Finish where
  | list | vectorTail | vectorFull
  deriving DecidableEq

def Finish.start : Finish → Nat
  | .list => 1524 | .vectorTail => 1360 | .vectorFull => 1580

def Finish.ops : Finish → List Tail.Op
  | .list => [.p1524, .p1528, .p1532]
  | .vectorTail => [.p1360, .p1364]
  | .vectorFull => [.p1580, .p1584]

def finishRegisters (kind : Finish) (s : ArmState) (size : Nat) : ArmState :=
  match kind with
  | .list => w (.GPR 8#5) (BitVec.ofNat 64 size) s
  | _ => s

@[irreducible] def finished (kind : Finish) (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) : ArmState :=
  w .PC (base + 1004#64)
    (write_mem_bytes 8 args.result (BitVec.ofNat 64 size) (finishRegisters kind s size))

def Finish.countReady (kind : Finish) (s : ArmState) (size : Nat) : Prop :=
  match kind with
  | .list => r (.GPR 23#5) s + 1#64 = BitVec.ofNat 64 size
  | _ => r (.GPR 24#5) s = BitVec.ofNat 64 size

theorem finish_run (kind : Finish) (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.start)
    (result : r (.GPR 19#5) s = args.result)
    (count : kind.countReady s size) :
    run kind.ops.length s = finished kind s base args size := by
  have follows : Tail.Follows base kind.ops s := by
    change r .PC s = _ at pc
    have stack := BoolCodec.stack_aligned s aligned
    change Aligned (r (.GPR 31#5) s) 4 at stack
    cases kind <;> simp [Finish.ops, Finish.start, Tail.Follows, Tail.Op.row, Tail.Op.effect,
      Activation.put, Activation.next, Dispatch.next, state_simp_rules,
      aligned, CheckSPAlignment, stack, pc, BitVec.add_assoc, BitVec.sub_eq_add_neg]
  rw [Tail.runs kind.ops s base code error follows]
  change r .PC s = _ at pc
  cases kind <;> simp only [Finish.countReady] at count
  all_goals
    simp [finished, finishRegisters, Finish.ops, Finish.start, Tail.block, Tail.Op.effect,
      Activation.put, Activation.next, Dispatch.next, state_simp_rules, result, count, pc,
      NatAdd.load_store_field, NatAdd.load_gpr_pc, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem finished_post (kind : Finish) (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat)
    (owned : Owned s args desc (.bits bits) size)
    (error : read_err s = .None) (result : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP)
    (bytes : SszNative.ByteView.BytesAt (widthLoad s) args.output.toNat
      (SszNative.Serialize.emit desc (.bits bits))) :
    Produced s (finished kind s base args size) args desc (.bits bits) size base := by
  have resultBound : args.result.toNat + 8 ≤ 2^64 := by have bound := owned.resultBound; omega
  have outputBound : args.output.toNat + size ≤ 2^64 := by
    have bound := owned.outputBound
    have fit := owned.fitting
    omega
  have outputProtected : Protected [(args.result.toNat, 8)] args.output.toNat size := by
    by_cases empty : size = 0
    · exact Or.inl empty
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rcases owned.outputResult with zero | separate
      · have fit := owned.fitting; omega
      · have apart := separate (args.result.toNat, 8) (by simp)
        have fit := owned.fitting
        simp only [Prod.fst, Prod.snd] at apart ⊢
        omega
  have inputMemory : (finishRegisters kind s size).mem = s.mem := by
    cases kind <;> simp [finishRegisters, state_simp_rules]
  have inputBytes : SszNative.ByteView.BytesAt (widthLoad (finishRegisters kind s size))
      args.output.toNat (SszNative.Serialize.emit desc (.bits bits)) := by
    rw [load_eq_of_mem_eq inputMemory]
    exact bytes
  have sizeEq := (SszNative.Serialize.expected_encoding desc (.bits bits)).2 size owned.expected
  have frame := Delimited.store_frame (finishRegisters kind s size) args.result 8
    (BitVec.ofNat 64 size) resultBound
  have storedBytes := frame.bytes args.output (SszNative.Serialize.emit desc (.bits bits))
    (by rw [sizeEq]; exact outputBound) (by rw [sizeEq]; exact outputProtected) inputBytes
  constructor
  · simp [finished, state_simp_rules]
  · cases kind <;> simp [finished, finishRegisters, state_simp_rules]
  · cases kind <;> simpa [finished, finishRegisters, state_simp_rules] using error
  · cases kind <;> simpa [finished, finishRegisters, state_simp_rules] using result
  · cases kind <;> simpa [finished, finishRegisters, state_simp_rules] using stack
  · simp only [finished, state_simp_rules]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ resultBound
  · have memory : (finished kind s base args size).mem =
        (write_mem_bytes 8 args.result (BitVec.ofNat 64 size) (finishRegisters kind s size)).mem := by
      simp only [finished, state_simp_rules]
    rw [load_eq_of_mem_eq memory]
    exact storedBytes
  · intro address outside
    have away := outside (args.result.toNat, 8) (by simp [bodyWrites])
    simp only [finished, state_simp_rules]
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address resultBound away]
    exact congrFun inputMemory address
  · intro reg member
    have other : reg ≠ 8#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    cases kind <;> simp [finished, finishRegisters, state_simp_rules, other]
  · intro reg low high
    cases kind <;> simp [finished, finishRegisters, state_simp_rules]

end SszArm.Emit.Bits
