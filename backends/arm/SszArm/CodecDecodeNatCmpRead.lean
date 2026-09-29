import SszArm.CodecDecodeNatCmpContract

namespace SszArm.Codec.Decode.NatCmpUsize

open SszNative.Limbs

def readOps (two : Bool) : List Op :=
  [.p84, .p88, .p92] ++ (if two then [.p96, .p100] else [.p112]) ++ [.p116]

/-- The physical length selects the high-word load even for redundantly padded
representations; the significant count only justifies numeric reconstruction. -/
theorem large_read (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (nonempty : 0 < words.length) (fits : sigWords words ≤ 2)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 84#64)
    (pointerAt : r (.GPR 0#5) s = pointer)
    (countAt : r (.GPR 1#5) s = BitVec.ofNat 64 words.length)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = base + 120#64 ∧
      wideValue t = value words := by
  have countBound : words.length < 2 ^ 64 := by have := source.2.1; omega
  have carry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
  change (AddWithCarry (BitVec.ofNat 64 words.length) 18446744073709551613#64 1#1).2.c =
    1#1 ↔ 2 ≤ words.length at carry
  have low : read_mem_bytes 8 pointer s = words[0]?.getD 0 := by
    simpa [List.getElem?_eq_getElem nonempty] using stored ⟨0, nonempty⟩
  change r .PC s = _ at pc
  by_cases two : 2 ≤ words.length
  · have high : read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0 := by
      simpa [List.getElem?_eq_getElem (by omega : 1 < words.length)] using stored ⟨1, by omega⟩
    let ops := readOps true
    have follows : Follows base ops s := by
      simp [ops, readOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, pc, countAt, carry, two, BitVec.add_assoc]
    refine ⟨ops.length, block base ops s, block_run base ops s code error aligned follows,
      readonly_frame base ops s (by decide), ?_, ?_⟩
    · simp [ops, readOps, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, pc, countAt, carry, two, BitVec.add_assoc]
    · have bound := SszNative.NatDivision.value_lt_128
        (SszNative.NatOperand.large pointer words) fits
      simp only [wideValue, Measure.Uint.pairValue]
      simp [ops, readOps, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, pointerAt, low, high]
      cases words with
      | nil => simp at two
      | cons lo rest =>
        cases rest with
        | nil => simp at two
        | cons hi rest =>
          simp only [SszNative.NatOperand.value, SszNative.NatOperand.words, value] at bound ⊢
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          have zero : value rest = 0 := by omega
          rw [zero]
          omega
  · let ops := readOps false
    have one : words.length = 1 := by omega
    have follows : Follows base ops s := by
      simp [ops, readOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, pc, countAt, carry, two, BitVec.add_assoc]
    refine ⟨ops.length, block base ops s, block_run base ops s code error aligned follows,
      readonly_frame base ops s (by decide), ?_, ?_⟩
    · simp [ops, readOps, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, pc, countAt, carry, two, BitVec.add_assoc]
    · simp [wideValue, Measure.Uint.pairValue, ops, readOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, pointerAt, low]
      cases words with
      | nil => simp at nonempty
      | cons lo rest =>
        have empty : rest = [] := List.eq_nil_of_length_eq_zero (by
          simp only [List.length_cons] at one
          omega)
        subst rest
        simp [value]

end SszArm.Codec.Decode.NatCmpUsize
