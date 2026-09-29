import SszArm.CodecFixedMeasureStatus

namespace SszArm.Codec.Fixed.MeasureFixed

open Dispatch.Block (next put)
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

def someOps : List Op := [.finish .p624, .finish .p628, .finish .p632, .finish .p636]

@[irreducible] def someResult (s : ArmState) : ArmState := block someOps s

def someMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 19#5) s) 1#64
    (write_mem_bytes 16 (r (.GPR 19#5) s + 8#64)
      (r (.GPR 22#5) s ++ r (.GPR 21#5) s) s)

@[simp] theorem some_memory (s : ArmState) : (someResult s).mem = (someMemory s).mem := by
  simp [someResult, someOps, block, Op.effect, Return.Op.effect, next, put,
    someMemory, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem some_pc (s : ArmState) : read_pc (someResult s) = read_pc s + 52#64 := by
  simp [someResult, someOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem some_program (s : ArmState) : (someResult s).program = s.program :=
  block_program someOps s

@[simp] theorem some_error (s : ArmState) : read_err (someResult s) = read_err s :=
  block_error someOps s

@[simp] theorem some_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (someResult s) = r (.SFP reg) s := by
  simp [someResult, someOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules]

theorem some_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 8#5) :
    r (.GPR reg) (someResult s) = r (.GPR reg) s := by
  simp [someResult, someOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules, different]

theorem some_run (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 624#64) :
    run 4 s = someResult s := by
  have pcs : PCs base someOps s := by
    change r .PC s = base + 624#64 at pc
    simp [PCs, someOps, Op.row, Return.Op.row, Op.effect, Return.Op.effect,
      put, next, state_simp_rules, pc, BitVec.add_assoc]
  exact run_block someOps s base code error aligned pcs

theorem some_frame (s : ArmState) (resultBound : (r (.GPR 19#5) s).toNat + 24 ≤ 2^64) :
    MemoryFrame [((r (.GPR 19#5) s).toNat, 24)] s (someResult s) := by
  intro address outside
  have apart := outside ((r (.GPR 19#5) s).toNat, 24) (by simp)
  simp only [Prod.fst, Prod.snd] at apart
  rw [some_memory]
  simp only [someMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address (by bv_omega) (by bv_omega)]

theorem some_words (s : ArmState) (resultBound : (r (.GPR 19#5) s).toNat + 24 ≤ 2^64) :
    read_mem_bytes 8 (r (.GPR 19#5) s) (someResult s) = 1#64 ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) (someResult s) = r (.GPR 21#5) s ∧
    read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) (someResult s) = r (.GPR 22#5) s := by
  simp only [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (some_memory s))]
  simp only [someMemory]
  simp (disch := bv_omega) only [UintCodec.Tail.write_pair_words, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, BoolCodec.read_mem_bytes_write_mem_bytes_same,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem some_observe (s : ArmState) (width : SszNative.NatOperand)
    (resultBound : (r (.GPR 19#5) s).toNat + 24 ≤ 2^64)
    (pointer : r (.GPR 21#5) s = width.pointer) (payload : r (.GPR 22#5) s = width.payload)
    (input : width.At (widthLoad s))
    (owned : NatDivision.OperandOwned [((r (.GPR 19#5) s).toNat, 24)] width) :
    widthLoad (someResult s) (r (.GPR 19#5) s).toNat 8 = some 1 ∧
      SszNative.NatArithmetic.operandAt (widthLoad (someResult s))
        ((r (.GPR 19#5) s).toNat + 8) width := by
  rcases some_words s resultBound with ⟨tag, low, high⟩
  have preserved := NatDivision.operand_at_preserved (some_frame s resultBound) width input owned
  refine ⟨?_, ?_, ?_, preserved⟩
  · simpa [widthLoad] using congrArg (fun word : BitVec 64 => some word.toNat) tag
  · simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, pointer] using
      congrArg (fun word : BitVec 64 => some word.toNat) low
  · simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc, payload] using
      congrArg (fun word : BitVec 64 => some word.toNat) high

end SszArm.Codec.Fixed.MeasureFixed
