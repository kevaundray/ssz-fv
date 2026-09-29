import SszArm.NatMulEntry
import SszArm.NatMulLoop
import SszArm.NatMulNormalizeReturn
import SszArm.NatMulReturnError

namespace SszArm.NatMul

open Delimited (Span Protected MemoryFrame)
open UintCodec (widthLoad)
open SszNative (NatOperand NatArithmetic)

 theorem large_operand_cover {large small : List Span} (cover : BitVector.Covers large small)
    (operand : NatOperand) (owned : NatAdd.OperandOwned large operand) :
    NatAdd.OperandOwned small operand := by
  cases operand with
  | small word => trivial
  | large pointer words => exact cover.protected owned

theorem large_count_bound (s : ArmState) (operand : NatOperand)
    (input : operand.At (widthLoad s)) : operand.wordCount < 2^64 := by
  have count := SszNative.Limbs.sigWords_le_length operand.words
  cases operand with
  | small word =>
    change SszNative.Limbs.sigWords [word] < 2^64
    simpa only [NatOperand.words, List.length_cons, List.length_nil] using
      (show SszNative.Limbs.sigWords [word] < 2^64 by
        have : SszNative.Limbs.sigWords [word] ≤ 1 := count
        omega)
  | large pointer words =>
    have physical := input.2.2.1
    change SszNative.Limbs.sigWords words < 2^64
    change SszNative.Limbs.sigWords words ≤ words.length at count
    omega

theorem large_sp_nat {s t : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (sp : r (.GPR 31#5) t = r (.GPR 31#5) s - 96#64) :
    (r (.GPR 31#5) t).toNat = (r (.GPR 31#5) s).toNat - 96 := by
  have bound := owned.stackBound
  rw [sp]
  bv_omega

theorem large_stack_local (s : ArmState) (result : NatArithmetic.Outcome NatOperand) :
    ((r (.GPR 31#5) s).toNat - 144, 144) ∈ localWrites s result := by
  cases value : result.result <;> simp [localWrites, value]

theorem large_local_cover (s : ArmState) (result : NatArithmetic.Outcome NatOperand) :
    BitVector.Covers (writesFor s result) (localWrites s result) := by
  intro span member
  refine ⟨span, ?_, le_rfl, le_rfl⟩
  cases allocation : result.allocation <;> simp [writesFor, allocation, member]

theorem large_slot_cover {s t : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (sp : r (.GPR 31#5) t = r (.GPR 31#5) s - 96#64)
    (bytes : Nat) (bound : bytes ≤ 48) :
    BitVector.Covers (localWrites s (outcome s left right))
      [((r (.GPR 31#5) t).toNat - bytes, bytes)] := by
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  have stack := owned.stackBound
  have current := large_sp_nat owned sp
  exact ⟨((r (.GPR 31#5) s).toNat - 144, 144), large_stack_local _ _, by omega, by omega⟩

theorem large_return_cover {s t : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (sp : r (.GPR 31#5) t = r (.GPR 31#5) s - 96#64)
    (out : BitVec 64) (output : out = r (.GPR 0#5) s)
    (result : NatOperand) (success : (outcome s left right).result = .ok result) :
    BitVector.Covers (localWrites s (outcome s left right)) (returnWrites t out) := by
  intro span member
  simp only [returnWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨(out.toNat, 16), by simp [localWrites, success, output], le_rfl, le_rfl⟩
  · exact ⟨(out.toNat + 64, 4), by simp [localWrites, success, output], le_rfl, le_rfl⟩
  · exact large_slot_cover owned sp 16 (by decide) _ (by simp)

theorem large_error_cover {s t : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (sp : r (.GPR 31#5) t = r (.GPR 31#5) s - 96#64)
    (out : BitVec 64) (output : out = r (.GPR 0#5) s)
    (failure : (outcome s left right).result = .error .scratchExhausted) :
    BitVector.Covers (localWrites s (outcome s left right)) (returnErrorWrites t out) := by
  intro span member
  simp only [returnErrorWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨(out.toNat, 68), by simp [localWrites, failure, output], le_rfl, le_rfl⟩
  · exact large_slot_cover owned sp 16 (by decide) _ (by simp)

/-- Reads use the original physical arena descriptor, not a future result. -/
theorem large_header_read {s t : ArmState} {writes : List Span}
    {left right : NatOperand} (owned : Owned s left right)
    (frame : MemoryFrame writes s t)
    (protection : Protected writes (r (.GPR 5#5) s).toNat 24)
    (offset : Nat) (bound : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) s := by
  have physical := owned.arenaBound
  have address : (r (.GPR 5#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 5#5) s).toNat + offset := by bv_omega
  apply frame.read
  · rw [address]; omega
  · rw [address]; exact protection.subspan offset 8 bound

theorem large_saved_frame {s u t : ArmState} {left right : NatOperand} {writes : List Span}
    (owned : Owned s left right) (saved : Saved s u)
    (frame : MemoryFrame writes u t)
    (protection : Protected writes (r (.GPR 31#5) u).toNat 96)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) u)
    (x29 : r (.GPR 29#5) t = r (.GPR 29#5) u)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) u).setWidth 64) : Saved s t := by
  refine ⟨sp.trans saved.sp, ?_, x29.trans saved.x29, ?_⟩
  · intro reg offset member
    have bound : offset + 8 ≤ 96 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h | h | h | h | h | h | h
      all_goals cases h <;> decide
    have space := ReturnSpace.of_owned owned saved
    have address : (r (.GPR 31#5) u + BitVec.ofNat 64 offset).toNat =
        (r (.GPR 31#5) u).toNat + offset := by
      have physical := space.savedBound
      bv_omega
    rw [sp]
    have same := frame.read (address := r (.GPR 31#5) u + BitVec.ofNat 64 offset)
      (bytes := 8) (by rw [address]; have := space.savedBound; omega)
      (by rw [address]; exact protection.subspan offset 8 bound)
    exact same.trans (saved.words reg offset member)
  · intro reg low high
    exact (vectors reg low high).trans (saved.vectors reg low high)

end SszArm.NatMul
