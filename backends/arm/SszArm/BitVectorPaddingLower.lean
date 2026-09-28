import SszArm.BitVectorPaddingExec

namespace SszArm.BitVector.Padding

open Block BoolCodec

/-- Only physical output versus the sixteen-byte lowering slot is separated. -/
structure Space (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  output : (r (.GPR 23#5) s).toNat + 80 ≤ 2^64
  separate : (r (.GPR 23#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 23#5) s).toNat

def Store.image (store : Store) (s : ArmState) : ArmState :=
  store.zeroImage (NatExact.spillTwo s (r (.GPR 9#5) s) (r (.GPR 10#5) s))

def Store.result (store : Store) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 store.stop) (store.image s)

macro "padding_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

macro "padding_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) (disch := padding_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

theorem image_spills (store : Store) (s : ArmState) (space : Space s) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (store.image s) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (store.image s) = r (.GPR 10#5) s := by
  obtain ⟨stack, output, separate⟩ := space
  cases store <;> constructor <;>
    simp only [Store.image, Store.zeroImage, Store.displacement, NatExact.spillTwo,
      reduceCtorEq, ↓reduceIte] <;> padding_reads

@[simp] theorem result_register (store : Store) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.GPR reg) (store.result s base) = r (.GPR reg) s := by
  cases store <;> simp [Store.result, Store.image, Store.zeroImage,
    NatExact.spillTwo, state_simp_rules]

@[simp] theorem result_program (store : Store) (s : ArmState) (base : BitVec 64) :
    (store.result s base).program = s.program := by
  cases store <;> simp [Store.result, Store.image, Store.zeroImage,
    NatExact.spillTwo, state_simp_rules]

@[simp] theorem result_error (store : Store) (s : ArmState) (base : BitVec 64) :
    read_err (store.result s base) = read_err s := by
  cases store <;> simp [Store.result, Store.image, Store.zeroImage,
    NatExact.spillTwo, state_simp_rules]

@[simp] theorem result_vector (store : Store) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (store.result s base) = r (.SFP reg) s := by
  cases store <;> simp [Store.result, Store.image, Store.zeroImage,
    NatExact.spillTwo, state_simp_rules]

@[simp] theorem result_pc (store : Store) (s : ArmState) (base : BitVec 64) :
    read_pc (store.result s base) = base + BitVec.ofNat 64 store.stop := by
  simp [Store.result, state_simp_rules]

theorem result_space (store : Store) (s : ArmState) (base : BitVec 64)
    (space : Space s) : Space (store.result s base) := by
  obtain ⟨stack, output, separate⟩ := space
  constructor
  · simpa only [result_register] using stack
  · simpa only [result_register] using output
  · simpa only [result_register] using separate

theorem result_aligned (store : Store) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (store.result s base) := by
  simpa only [CheckSPAlignment, state_simp_rules, result_register] using aligned

private theorem lower_summary (store : Store) (s : ArmState) (base : BitVec 64)
    (space : Space s) (pc : read_pc s = base + BitVec.ofNat 64 store.start) :
    restoreResult (store.bodyResult (saveResult s)) = store.result s base := by
  have spills := image_spills store s space
  have hpc : r .PC s = base + BitVec.ofNat 64 store.start := pc
  cases store <;>
    simp only [Store.image, Store.zeroImage, Store.displacement, NatExact.spillTwo,
      reduceCtorEq, ↓reduceIte, state_simp_rules, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd] at spills <;>
    simp (config := {decide := true, instances := true}) only
      [restoreResult, Store.bodyResult, saveResult, Store.result, Store.image,
       Store.zeroImage, Store.displacement, Store.bodyOps, Store.start, Store.stop,
       NatExact.spillTwo, List.length_cons, List.length_nil, reduceCtorEq, ↓reduceIte,
       Nat.reduceMul, Nat.reduceAdd, NatExact.store_w, NatExact.gpr_w_pc,
       state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
       BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, BitVec.add_zero, BitVec.zero_add,
       BitVec.sub_add_cancel, spills.1, spills.2, hpc, w_of_w_shadow] <;>
    apply congrArg (w .PC _) <;>
    apply NatExact.restore_spill_registers <;>
    simp (config := {decide := true}) [NatExact.r_gpr_w, state_simp_rules]

/-- Three independently decoded bounded blocks, with restored spill registers. -/
theorem lower_run (store : Store) (s : ArmState) (base : BitVec 64)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 store.start) :
    run (3 + (store.bodyOps.length + 3)) s = store.result s base := by
  have first := save_run store s base code error aligned pc
  have hpc : r .PC s = base + BitVec.ofNat 64 store.start := pc
  have savedCode : CodeAt (saveResult s) base := by
    simpa only [CodeAt, saveResult, NatExact.spillTwo, state_simp_rules] using code
  have savedError : read_err (saveResult s) = .None := by
    simpa [saveResult, NatExact.spillTwo, state_simp_rules] using error
  have stack := stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have savedAligned : CheckSPAlignment (saveResult s) := by
    simpa (config := {decide := true, instances := true})
      [saveResult, NatExact.spillTwo, CheckSPAlignment, state_simp_rules,
       bitvec_rules, minimal_theory] using aligned_sub16 _ stack
  have savedPC : read_pc (saveResult s) = base + BitVec.ofNat 64 store.bodyStart := by
    cases store <;> simpa [saveResult, Store.start, Store.bodyStart, state_simp_rules,
      BitVec.add_assoc] using congrArg (fun x => x + 12#64) pc
  have second := body_run store (saveResult s) base savedCode savedError savedPC
  have bodyCode : CodeAt (store.bodyResult (saveResult s)) base := by
    cases store <;> simpa only [CodeAt, Store.bodyResult, Store.zeroImage,
      reduceCtorEq, ↓reduceIte, state_simp_rules] using savedCode
  have bodyError : read_err (store.bodyResult (saveResult s)) = .None := by
    cases store <;> simpa [Store.bodyResult, Store.zeroImage, state_simp_rules] using savedError
  have bodyAligned : CheckSPAlignment (store.bodyResult (saveResult s)) := by
    cases store <;> simpa [Store.bodyResult, Store.zeroImage, CheckSPAlignment,
      state_simp_rules] using savedAligned
  have bodyPC : read_pc (store.bodyResult (saveResult s)) =
      base + BitVec.ofNat 64 store.restoreStart := by
    cases store <;> simp [Store.bodyResult, Store.bodyOps, Store.restoreStart,
      Store.bodyStart, Store.start, saveResult, state_simp_rules, hpc, BitVec.add_assoc]
  have third := restore_run store (store.bodyResult (saveResult s)) base
    bodyCode bodyError bodyAligned bodyPC
  rw [run_plus, first, run_plus, second, third]
  exact lower_summary store s base space pc

end SszArm.BitVector.Padding
