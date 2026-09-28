import SszArm.MeasureUintWidthScan
import SszArm.MeasureUintCompare
import SszNatNarrow

namespace SszArm.Measure.Uint

open SszNative.Limbs

theorem two_limb_value (words : List (BitVec 64)) (fits : sigWords words ≤ 2) :
    pairValue (words[0]?.getD 0#64) (words[1]?.getD 0#64) = SszNative.Limbs.value words := by
  have bound := SszNative.NatDivision.value_lt_128
    (SszNative.NatOperand.large 0#64 words) fits
  cases words with
  | nil => simp [pairValue, SszNative.Limbs.value]
  | cons low rest =>
    cases rest with
    | nil => simp [pairValue, SszNative.Limbs.value]
    | cons high rest =>
      simp only [SszNative.NatOperand.value, SszNative.NatOperand.words,
        SszNative.Limbs.value] at bound
      have zero : SszNative.Limbs.value rest = 0 := by omega
      simp [pairValue, SszNative.Limbs.value, zero]

def widthReadOps (length : Nat) : List WidthOp :=
  [.p2880, .p2884, .p2888] ++
    if 2 ≤ length then [.p2892, .p2896] else [.p3012, .p3016]

/-- The physical length controls one-versus-two loads, whereas significant
length controls rejection. Consequently padded zeros and one-limb arrays work. -/
theorem width_read (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2880#64)
    (pointerReg : r (.GPR 21#5) s = pointer)
    (countReg : r (.GPR 20#5) s = BitVec.ofNat 64 words.length)
    (source : NatCompare.Source s pointer words) (memory : NatCompare.Words s pointer words)
    (nonempty : 0 < words.length) (fits : sigWords words ≤ 2) :
    ∃ t, run 5 s = t ∧ NatNarrow.Frame s t ∧ read_pc t = base + 3912#64 ∧
      pairValue (r (.GPR 10#5) t) (r (.GPR 11#5) t) = SszNative.Limbs.value words ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s := by
  let ops := widthReadOps words.length
  let t := widthBlock base ops s
  have pc' : r .PC s = base + 2880#64 := pc
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have carry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  have branchCarry :
      (AddWithCarry (BitVec.ofNat 64 words.length) 18446744073709551613#64 1#1).2.c = 1#1 ↔
        2 ≤ words.length := carry
  have low : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
    simpa [List.getElem?_eq_getElem nonempty] using memory ⟨0, nonempty⟩
  have high : 2 ≤ words.length → read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0#64 := by
    intro two
    simpa [List.getElem?_eq_getElem (by omega : 1 < words.length)] using memory ⟨1, by omega⟩
  have noHigh : ¬ 2 ≤ words.length → words[1]?.getD 0#64 = 0#64 := by
    intro one
    cases words with
    | nil => simp
    | cons first rest =>
      have short : (first :: rest).length < 2 := Nat.lt_of_not_ge one
      simp only [List.length_cons] at short
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [empty]
  have follows : WidthFollows base ops s := by
    by_cases two : 2 ≤ words.length <;>
      simp [ops, widthReadOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next,
        compare64, Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules,
        pc', countReg, branchCarry, two, BitVec.add_assoc]
  have length : ops.length = 5 := by
    dsimp only [ops, widthReadOps]; split <;> rfl
  refine ⟨t, ?_, width_pure_frame base ops s ?_, ?_, ?_, ?_, ?_⟩
  · rw [← length]
    exact width_run base ops s code error aligned follows
  · dsimp only [ops, widthReadOps]; split <;> decide
  · by_cases two : 2 ≤ words.length <;>
      simp [t, ops, widthReadOps, widthBlock, WidthOp.effect, put, next,
        compare64, Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules,
        countReg, two]
  · rw [← two_limb_value words fits]
    by_cases two : 2 ≤ words.length
    · simp [t, ops, widthReadOps, widthBlock, WidthOp.effect, put, next,
        compare64, Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules,
        pointerReg, two, low, high two]
    · simp [t, ops, widthReadOps, widthBlock, WidthOp.effect, put, next,
        compare64, Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules,
        pointerReg, two, low, noHigh two]
  · by_cases two : 2 ≤ words.length <;>
      simp [t, ops, widthReadOps, widthBlock, WidthOp.effect, put, next,
        compare64, Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, two]
  · by_cases two : 2 ≤ words.length <;>
      simp [t, ops, widthReadOps, widthBlock, WidthOp.effect, put, next,
        compare64, Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, two]

end SszArm.Measure.Uint
