import SszArm.MeasureBitsPropagationFrame

namespace SszArm.Measure.Bits.Propagation

open UintCodec (widthLoad)

macro "measure_propagation_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

theorem finish_payload (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64)
    (offset bytes : Nat) (within : 16 ≤ offset ∧ offset + bytes ≤ 64) :
    widthLoad (Stage.finish.result s base) ((r (.GPR 19#5) s).toNat + offset) bytes =
      widthLoad s ((r (.GPR 19#5) s).toNat + offset) bytes := by
  simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, Stage.result, state_simp_rules]
  simp (disch := measure_propagation_side)
    [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem finish_leading (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    widthLoad (Stage.finish.result s base) (r (.GPR 19#5) s).toNat 8 =
      some (r (.GPR 21#5) s).toNat ∧
    widthLoad (Stage.finish.result s base) ((r (.GPR 19#5) s).toNat + 8) 8 =
      some (r (.GPR 20#5) s).toNat := by
  constructor <;>
    simp (config := {decide := true, instances := true}) (disch := measure_propagation_side)
      [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, Stage.result, state_simp_rules,
        UintCodec.Tail.write_pair_words, BoolCodec.read_mem_bytes_write_mem_bytes_same,
        BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem finish_status (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    widthLoad (Stage.finish.result s base) ((r (.GPR 19#5) s).toNat + 64) 4 =
      some ((r (.GPR 22#5) s).setWidth 32).toNat := by
  simp (config := {decide := true, instances := true}) (disch := measure_propagation_side)
    [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, Stage.result, state_simp_rules,
      write_pair_dwords, BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem finish_at (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64)
    (leading : r (.GPR 21#5) s = 1#64)
    (length : r (.GPR 20#5) s = 0#64)
    (status : (r (.GPR 22#5) s).setWidth 32 = 32768#32)
    (copied : ∀ index : Fin 6,
      widthLoad s ((r (.GPR 19#5) s).toNat + (16 + 8 * index.val)) 8 = some 0) :
    ResultAt (widthLoad (Stage.finish.result s base)) (r (.GPR 19#5) s).toNat
      (.error (.arithmetic .scratchExhausted)) := by
  have first := finish_leading s base physical
  have flag := finish_status s base physical
  have payload : ∀ index : Fin 6,
      widthLoad (Stage.finish.result s base)
        ((r (.GPR 19#5) s).toNat + (16 + 8 * index.val)) 8 = some 0 := by
    intro index
    rw [finish_payload s base physical (16 + 8 * index.val) 8 (by have := index.isLt; omega)]
    exact copied index
  change ErrorAt _ _ (.arithmetic .scratchExhausted)
  refine ⟨?_, ?_, ⟨?_, ?_, trivial⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  · simpa only [leading, BitVec.toNat_ofNat] using first.1
  · simpa only [length, BitVec.toNat_ofNat] using first.2
  · simpa [errorOperands, SszNative.NatOperand.pointer, BitVec.toNat_ofNat] using payload 0
  · simpa [errorOperands, SszNative.NatOperand.payload, BitVec.toNat_ofNat, Nat.add_assoc] using payload 1
  · simpa [errorOperands, SszNative.NatOperand.pointer, BitVec.toNat_ofNat] using payload 2
  · simpa [errorOperands, SszNative.NatOperand.payload, BitVec.toNat_ofNat, Nat.add_assoc]
      using payload ⟨3, by decide⟩
  · exact payload 4
  · exact payload 5
  · simpa only [status, errorCode, BitVec.toNat_ofNat] using flag

end SszArm.Measure.Bits.Propagation
