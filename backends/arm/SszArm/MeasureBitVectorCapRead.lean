import SszArm.MeasureBitVectorCapReadSteps

namespace SszArm.Measure.BitVector

open Result

def capReadOps (length : Nat) : List Op :=
  [p2832, p2836, p2840] ++ (if 2 ≤ length then [p2844, p2848] else [p2992]) ++ [p2996, p3000]

@[irreducible] def capReadResult (s : ArmState) (length : Nat) : ArmState := effect (capReadOps length) s

macro "measure_bitvector_cap_read_expand" branch:term : tactic =>
  `(tactic|
    (simp only [capReadResult, capReadOps, ($branch), ↓reduceIte]
     all_goals simp_all (config := {decide := true, instances := true})
       [effect, Follows,
     cap_read2832_effect, cap_read2836_effect, cap_read2840_effect,
     cap_read2844_effect, cap_read2848_effect, cap_read2992_effect,
     cap_read2996_effect, cap_read3000_effect,
     show p2832.offset = 2832 from rfl, show p2836.offset = 2836 from rfl,
     show p2840.offset = 2840 from rfl, show p2844.offset = 2844 from rfl,
     show p2848.offset = 2848 from rfl, show p2992.offset = 2992 from rfl,
     show p2996.offset = 2996 from rfl, show p3000.offset = 3000 from rfl,
     state_simp_rules, NatExact.r_gpr_w, BitVec.add_assoc]))

theorem cap_read (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2832#64) (ptr : r (.GPR 11#5) s = pointer)
    (count : r (.GPR 10#5) s = BitVec.ofNat 64 words.length)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words)
    (nonempty : 0 < words.length) :
    let t := capReadResult s words.length
    run (capReadOps words.length).length s = t ∧ CapFrame s t ∧
      read_pc t = base + 3268#64 ∧ r (.GPR 10#5) t = words[0]?.getD 0#64 ∧
      r (.GPR 11#5) t = words[1]?.getD 0#64 := by
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have carry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  have low : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
    simpa [List.getElem?_eq_getElem nonempty] using stored ⟨0, nonempty⟩
  have high : 2 ≤ words.length → read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0#64 := by
    intro two
    simpa [List.getElem?_eq_getElem (by omega : 1 < words.length)] using stored ⟨1, by omega⟩
  have noHigh : ¬2 ≤ words.length → words[1]?.getD 0#64 = 0#64 := by
    intro one
    cases words with
    | nil => simp
    | cons first rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by
        have lengthBound : rest.length + 1 < 2 := Nat.lt_of_not_ge one
        omega)
      simp [empty]
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (capReadOps words.length) s := by
    by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [capReadResult] using runs _ s base code follows
  · constructor
    · by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two
    · by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two
    · intro reg outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two
    · intro reg
      by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two
    · intro address outside
      by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two
  all_goals by_cases two : 2 ≤ words.length <;> measure_bitvector_cap_read_expand two

end SszArm.Measure.BitVector
