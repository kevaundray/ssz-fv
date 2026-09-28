import SszArm.MeasureActivationOps
import SszArm.BoolActivation
import SszArm.UintResultMemory

namespace SszArm.Measure

open Activation
open Delimited (MemoryFrame)

def prologueOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p20]

@[irreducible] def prologue (s : ArmState) : ArmState := Activation.block prologueOps s

def savedRegisters : List (BitVec 5 × Nat) :=
  [(29#5, 192), (30#5, 200), (26#5, 208), (25#5, 216), (24#5, 224),
   (23#5, 232), (22#5, 240), (21#5, 248), (20#5, 256), (19#5, 264)]

/-- Exactly the five paired writes executed after SUB SP,SP,272. -/
def savedMemory (s : ArmState) : ArmState :=
  let sp := (Args.ofEntry s).bodySP
  write_mem_bytes 16 (sp + 256#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
  (write_mem_bytes 16 (sp + 240#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
  (write_mem_bytes 16 (sp + 224#64) (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
  (write_mem_bytes 16 (sp + 208#64) (r (.GPR 25#5) s ++ r (.GPR 26#5) s)
  (write_mem_bytes 16 (sp + 192#64) (r (.GPR 30#5) s ++ r (.GPR 29#5) s) s))))

@[simp] theorem prologue_sp (s : ArmState) :
    r (.GPR 31#5) (prologue s) = (Args.ofEntry s).bodySP := by
  simp [prologue, prologueOps, Activation.block, Op.effect, put, next, save,
    Args.ofEntry, Args.bodySP, state_simp_rules]

@[simp] theorem prologue_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 31#5) :
    r (.GPR reg) (prologue s) = r (.GPR reg) s := by
  simp [prologue, prologueOps, Activation.block, Op.effect, put, next, save,
    different, state_simp_rules]

@[simp] theorem prologue_pc (s : ArmState) : read_pc (prologue s) = read_pc s + 24#64 := by
  simp [prologue, prologueOps, Activation.block, Op.effect, put, next, save,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (s : ArmState) : (prologue s).program = s.program := by
  simp [prologue, prologueOps, Activation.block]

@[simp] theorem prologue_error (s : ArmState) : read_err (prologue s) = read_err s := by
  simp [prologue, prologueOps, Activation.block]

@[simp] theorem prologue_memory (s : ArmState) : (prologue s).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, Activation.block, Op.effect, put, next, save,
    savedMemory, Args.ofEntry, Args.bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem prologue_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (prologue s) = r (.SFP reg) s := by
  simp [prologue, prologueOps, Activation.block, Op.effect, put, next, save, state_simp_rules]

theorem bodySP_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    Aligned (Args.ofEntry s).bodySP 4 := by
  simp (config := {decide := true}) [CheckSPAlignment, read_gpr, Args.ofEntry, Args.bodySP,
    Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
  bv_omega

theorem prologue_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (prologue s) :=
  CheckSPAlignment_of_r_sp_aligned (prologue_sp s) (bodySP_aligned s aligned)

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 6 s = prologue s := by
  have afterSP := bodySP_aligned s aligned
  have follows : Follows base prologueOps s := by
    change r .PC s = base at pc
    simp (config := {decide := true}) [Follows, prologueOps, Op.row, Op.effect,
      put, next, save, state_simp_rules, CheckSPAlignment, read_gpr,
      BitVec.setWidth_eq, Args.ofEntry, Args.bodySP, pc, BitVec.add_assoc] at aligned afterSP ⊢
    exact ⟨aligned, afterSP⟩
  rw [prologue]
  have execution := Activation.runs prologueOps s base code error follows
  change run 6 s = Activation.block prologueOps s at execution
  exact execution

theorem prologue_frame (s : ArmState) (low : 288 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (saveWrites (Args.ofEntry s)) s (prologue s) := by
  intro a outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 80, 80) (by simp [saveWrites, Args.ofEntry])
  simp only [Prod.fst, Prod.snd] at apart
  rw [prologue_memory]
  simp only [savedMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ a
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)]

theorem prologue_saved (s : ArmState) (low : 288 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 offset) (prologue s) =
      r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (prologue_memory s))]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [savedMemory]
    simp (disch := (simp only [Args.bodySP, Args.ofEntry]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

end SszArm.Measure
