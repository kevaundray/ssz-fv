import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)

def fieldsSetupOps (progressive : Bool) : List Op :=
  (if progressive then [.p80, .p84] else [.p88]) ++ [.p92, .p96, .p100, .p104]

def fieldsOffset (progressive : Bool) : BitVec 64 := if progressive then 24 else 8

theorem fields_setup_pcs (s : ArmState) (base : BitVec 64) (progressive : Bool)
    (pc : read_pc s = base + if progressive then 80#64 else 88#64) :
    PCs base (fieldsSetupOps progressive) s := by
  change r .PC s = _ at pc
  cases progressive <;> simp [fieldsSetupOps, PCs, Op.row, Op.effect, next, put,
    loadPair, state_simp_rules, pc, BitVec.add_assoc]

theorem fields_setup_run (s : ArmState) (base : BitVec 64) (progressive : Bool)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + if progressive then 80#64 else 88#64) :
    run (fieldsSetupOps progressive).length s = block (fieldsSetupOps progressive) s :=
  run_block _ _ _ code error aligned (fields_setup_pcs s base progressive pc)

theorem fields_setup_pc (s : ArmState) (base : BitVec 64) (progressive : Bool)
    (pc : read_pc s = base + if progressive then 80#64 else 88#64) :
    read_pc (block (fieldsSetupOps progressive) s) = base + 108#64 := by
  change r .PC s = _ at pc
  cases progressive <;> simp [fieldsSetupOps, block, Op.effect, next, put,
    loadPair, state_simp_rules, pc, BitVec.add_assoc]

theorem field_count_word (count : Nat) (bound : 24 * count < 2^64) :
    ((BitVec.ofNat 64 count + (BitVec.ofNat 64 count <<< 1)) <<< 3) =
      BitVec.ofNat 64 (24 * count) := by
  bv_omega

theorem fields_setup_arguments (s : ArmState) (progressive : Bool) (pointer : BitVec 64)
    (count : Nat) (bound : 24 * count < 2^64)
    (pointerAt : read_mem_bytes 8 (r (.GPR 0#5) s + fieldsOffset progressive) s = pointer)
    (countAt : read_mem_bytes 8 (r (.GPR 0#5) s + fieldsOffset progressive + 8#64) s =
      BitVec.ofNat 64 count) :
    r (.GPR 8#5) (block (fieldsSetupOps progressive) s) = pointer ∧
    r (.GPR 19#5) (block (fieldsSetupOps progressive) s) = BitVec.ofNat 64 (24 * count) := by
  cases progressive <;>
    simp only [fieldsSetupOps, fieldsOffset, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.cons_append, block, List.foldl_cons, List.foldl_nil,
      Op.effect, next, put, loadPair, state_simp_rules, BitVec.add_assoc,
      show 0#64 + 8#64 = 8#64 from rfl, BitVec.add_zero] at pointerAt countAt ⊢
  all_goals rw [pointerAt, countAt, field_count_word count bound]
  all_goals exact ⟨rfl, rfl⟩

theorem fields_setup_memory (s : ArmState) (progressive : Bool) :
    (block (fieldsSetupOps progressive) s).mem = s.mem := by
  cases progressive <;> simp [fieldsSetupOps, block, Op.effect, next, put,
    loadPair, state_simp_rules]

theorem fields_setup_register (s : ArmState) (progressive : Bool) (reg : BitVec 5)
    (different : reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 19#5) :
    r (.GPR reg) (block (fieldsSetupOps progressive) s) = r (.GPR reg) s := by
  rcases different with ⟨h8, h9, h19⟩
  cases progressive <;> simp [fieldsSetupOps, block, Op.effect, next, put,
    loadPair, state_simp_rules, h8, h9, h19]

theorem BodyContext.fields_setup {source current : ArmState}
    (context : BodyContext source current) (progressive : Bool) :
    BodyContext source (block (fieldsSetupOps progressive) current) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(fields_setup_register current progressive 31#5 (by decide)).trans context.saved.sp,
      ?_, ?_, ?_⟩
    all_goals rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (fields_setup_memory current progressive))]
    · exact context.saved.link
    · exact context.saved.first
    · exact context.saved.second
  · intro reg lower upper h19 h20 h30
    exact (fields_setup_register current progressive reg ⟨by bv_omega, by bv_omega, h19⟩).trans
      (context.registers reg lower upper h19 h20 h30)
  · intro reg lower upper
    rw [block_vector]
    exact context.vectors reg lower upper

end SszArm.Codec.Fixed.IsFixed
