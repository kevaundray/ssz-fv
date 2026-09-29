import SszArm.CodecDecodeBoundedOps

namespace SszArm.Codec.Decode.Bounded

def tagOps : List Op := [.p16, .p20, .p24, .p28]

def tagRead (s : ArmState) (base : BitVec 64) : ArmState :=
  let tag := read_mem_bytes 4 (r (.GPR 1#5) s) s
  w .PC (if tag = 1#32 then base + 32#64 else base + 196#64)
    (write_pstate (AddWithCarry tag (~~~1#32) 1#1).2
      (w (.GPR 19#5) (r (.GPR 0#5) s) (w (.GPR 8#5) (tag.setWidth 64) s)))

private theorem compare_zero32 (tag number : BitVec 32) :
    (AddWithCarry tag (~~~number) 1#1).2.z = 1#1 ↔ tag = number := by
  have result : (AddWithCarry tag (~~~number) 1#1).1 = tag - number := by
    simp only [fst_AddWithCarry_eq_sub_neg, BitVec.not_not]
  change (if (AddWithCarry tag (~~~number) 1#1).1 = 0#32 then 1#1 else 0#1) = 1#1 ↔ _
  rw [result]
  by_cases equal : tag = number
  · simp [equal]
  · have different : tag - number ≠ 0#32 := by bv_omega
    simp [equal, different]

theorem tag_zero (tag : BitVec 32) :
    (AddWithCarry tag 4294967294#32 1#1).2.z = 1#1 ↔ tag = 1#32 :=
  compare_zero32 tag 1#32

theorem tag_effect (s : ArmState) (base : BitVec 64) :
    block base tagOps s = tagRead s base := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases eight : reg = 8#5 <;> by_cases nineteen : reg = 19#5 <;>
        (try subst reg) <;>
        simp_all [block, tagOps, Op.effect, put, next, compare32, tagRead,
          state_simp_rules, BitVec.setWidth_setWidth_of_le]
    | PC => simp [block, tagOps, Op.effect, put, next, compare32, tagRead,
        state_simp_rules, BitVec.setWidth_setWidth_of_le, tag_zero]
    | SFP reg => simp [block, tagOps, Op.effect, put, next, compare32, tagRead, state_simp_rules]
    | FLAG flag => cases flag <;>
        simp [block, tagOps, Op.effect, put, next, compare32, tagRead,
          state_simp_rules, BitVec.setWidth_setWidth_of_le]
    | ERR => simp [block, tagOps, Op.effect, put, next, compare32, tagRead, state_simp_rules]
  · simp [block, tagOps, Op.effect, put, next, compare32, tagRead, state_simp_rules]
  · intro width address
    simp [block, tagOps, Op.effect, put, next, compare32, tagRead, state_simp_rules]

theorem tag_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 16#64) : run 4 s = tagRead s base := by
  have follows : Follows base tagOps s := by
    change r .PC s = _ at pc
    simp [tagOps, Follows, Op.row, Op.effect, put, next, compare32,
      state_simp_rules, pc, BitVec.add_assoc]
  exact (block_run base tagOps s code error aligned follows).trans (tag_effect s base)

def callOps : List Op := [.p32, .p36, .p40, .p44, .p48, .p52]

def prepared (s : ArmState) (base : BitVec 64) : ArmState :=
  let capPointer := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
  let capPayload := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s
  let actualPointer := read_mem_bytes 8 (r (.GPR 2#5) s) s
  let actualPayload := read_mem_bytes 8 (r (.GPR 2#5) s + 8#64) s
  w .PC (base - 78128#64)
    (w (.GPR 30#5) (base + 56#64)
      (w (.GPR 3#5) capPayload (w (.GPR 2#5) capPointer
        (w (.GPR 1#5) actualPayload (w (.GPR 0#5) actualPointer
          (w (.GPR 20#5) (r (.GPR 2#5) s)
            (w (.GPR 22#5) capPayload (w (.GPR 21#5) capPointer s))))))))

theorem call_effect (s : ArmState) (base : BitVec 64) :
    block base callOps s = prepared s base := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules,
        BitVec.add_assoc]
      simp only [r, w, read_base_gpr, write_base_gpr, write_base_pc, read_store, write_store]
    | PC => simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules]
    | SFP reg => simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules]
    | FLAG flag => simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules]
    | ERR => simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules]
  · simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules]
  · intro width address
    simp [block, callOps, Op.effect, loadPair, put, next, prepared, state_simp_rules]

theorem call_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 32#64) : run 6 s = prepared s base := by
  have follows : Follows base callOps s := by
    change r .PC s = _ at pc
    simp [callOps, Follows, Op.row, Op.effect, loadPair, put, next,
      state_simp_rules, pc, BitVec.add_assoc]
  exact (block_run base callOps s code error aligned follows).trans (call_effect s base)

end SszArm.Codec.Decode.Bounded
