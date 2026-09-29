import SszArm.CodecMeasureSingletonActivationOps

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open Activation
open SszArm.Measure.Activation (next put save)
open Delimited (MemoryFrame)

def bodySP (s : ArmState) : BitVec 64 := r (.GPR 31) s - 32#64

def prologueOps : List Activation.Op := [.enter, .saveLink, .savePair]

@[irreducible] def entered (s : ArmState) : ArmState := Activation.block prologueOps s

def savedMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 16#64) (r (.GPR 19) s ++ r (.GPR 20) s)
    (write_mem_bytes 8 (bodySP s) (r (.GPR 30) s) s)

def saveSpans (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31) s).toNat - 32, 8), ((r (.GPR 31) s).toNat - 16, 16)]

@[simp] theorem entered_sp (s : ArmState) : r (.GPR 31) (entered s) = bodySP s := by
  simp [entered, prologueOps, Activation.block, Activation.Op.effect,
    bodySP, next, put, save, state_simp_rules]

@[simp] theorem entered_pc (s : ArmState) : read_pc (entered s) = read_pc s + 12#64 := by
  simp [entered, prologueOps, Activation.block, Activation.Op.effect,
    next, put, save, state_simp_rules, BitVec.add_assoc]

@[simp] theorem entered_program (s : ArmState) : (entered s).program = s.program := by
  simp [entered, prologueOps, Activation.block]

@[simp] theorem entered_error (s : ArmState) : read_err (entered s) = read_err s := by
  simp [entered, prologueOps, Activation.block]

@[simp] theorem entered_memory (s : ArmState) : (entered s).mem = (savedMemory s).mem := by
  simp [entered, prologueOps, Activation.block, Activation.Op.effect,
    savedMemory, bodySP, next, put, save, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem entered_register (s : ArmState) (reg : BitVec 5) (notStack : reg ≠ 31#5) :
    r (.GPR reg) (entered s) = r (.GPR reg) s := by
  simp [entered, prologueOps, Activation.block, Activation.Op.effect,
    next, put, save, state_simp_rules, notStack]

@[simp] theorem entered_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (entered s) = r (.SFP reg) s := by
  simp [entered, prologueOps, Activation.block, Activation.Op.effect,
    next, put, save, state_simp_rules]

theorem bodySP_aligned (s : ArmState) (aligned : CheckSPAlignment s) : Aligned (bodySP s) 4 := by
  have first := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  have second := BoolCodec.aligned_sub16 _ first
  have position : (r (.GPR 31) s - 16#64) - 16#64 = bodySP s := by unfold bodySP; bv_omega
  rwa [position] at second

theorem entered_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (entered s) := by
  change Aligned (r (.GPR 31) (entered s)) 4
  rw [entered_sp]
  exact bodySP_aligned s aligned

theorem entered_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) : run 3 s = entered s := by
  have afterSP := bodySP_aligned s aligned
  rw [entered]
  apply Activation.runs prologueOps s base code error
  change r .PC s = base at pc
  simp (config := {decide := true}) [Activation.Follows, prologueOps, Activation.Op.row,
    Activation.Op.effect, next, put, save, state_simp_rules, CheckSPAlignment, read_gpr,
    BitVec.setWidth_eq, bodySP, pc, BitVec.add_assoc] at aligned afterSP ⊢
  exact ⟨aligned, afterSP⟩

def savedRegisters : List (BitVec 5 × Nat) := [(30, 0), (20, 16), (19, 24)]

theorem entered_saved (s : ArmState) (low : 32 ≤ (r (.GPR 31) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (entered s) = r (.GPR reg) s := by
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (entered_memory s)]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [savedMemory]
    simp (disch := (simp only [bodySP]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BitVec.add_zero, BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

theorem entered_frame (s : ArmState) (low : 32 ≤ (r (.GPR 31) s).toNat) :
    MemoryFrame (saveSpans s) s (entered s) := by
  intro address outside
  have first := outside ((r (.GPR 31) s).toNat - 32, 8) (by simp [saveSpans])
  have second := outside ((r (.GPR 31) s).toNat - 16, 16) (by simp [saveSpans])
  rw [entered_memory]
  simp only [savedMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address
    (by unfold bodySP; bv_omega) (by unfold bodySP; dsimp at second; bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address
    (by unfold bodySP; bv_omega) (by unfold bodySP; dsimp at first; bv_omega)

end SszArm.Codec.Measure.Singleton
