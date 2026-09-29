import SszArm.CodecFixedBlocks
import SszArm.CodecFixedContract
import SszArm.UintResultMemory

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)
open Delimited (MemoryFrame)

def prologueOps : List Op := [.p0, .p4, .p8]

@[irreducible] def prologue (s : ArmState) : ArmState := block prologueOps s

def bodySP (s : ArmState) : BitVec 64 := r (.GPR 31#5) s - 32#64

def savedMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 16#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
    (write_mem_bytes 8 (bodySP s) (r (.GPR 30#5) s) s)

@[simp] theorem prologue_sp (s : ArmState) : r (.GPR 31#5) (prologue s) = bodySP s := by
  simp [prologue, prologueOps, block, Op.effect, next, put, save, bodySP, state_simp_rules]

@[simp] theorem prologue_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 31#5) :
    r (.GPR reg) (prologue s) = r (.GPR reg) s := by
  simp [prologue, prologueOps, block, Op.effect, next, put, save, different, state_simp_rules]

@[simp] theorem prologue_pc (s : ArmState) : read_pc (prologue s) = read_pc s + 12#64 := by
  simp [prologue, prologueOps, block, Op.effect, next, put, save,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (s : ArmState) : (prologue s).program = s.program := by
  simp only [prologue, block_program]

@[simp] theorem prologue_error (s : ArmState) : read_err (prologue s) = read_err s := by
  simp only [prologue, block_error]

@[simp] theorem prologue_memory (s : ArmState) : (prologue s).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, block, Op.effect, next, put, save,
    savedMemory, bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem prologue_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (prologue s) := by
  rw [prologue]
  exact block_aligned _ _ aligned

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 3 s = prologue s := by
  rw [prologue]
  apply run_block prologueOps s base code error aligned
  change r .PC s = base at pc
  simp [PCs, prologueOps, Op.row, Op.effect, next, put, save,
    state_simp_rules, pc, BitVec.add_assoc]

theorem prologue_frame (s : ArmState) (low : 32 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (Stack.envelope (r (.GPR 31#5) s).toNat 32) s (prologue s) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [Stack.envelope])
  simp only [Prod.fst, Prod.snd] at apart
  rw [prologue_memory]
  simp only [savedMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address
    (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address
    (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)

structure Saved (s t : ArmState) : Prop where
  sp : r (.GPR 31#5) t = bodySP s
  link : read_mem_bytes 8 (bodySP s) t = r (.GPR 30#5) s
  first : read_mem_bytes 8 (bodySP s + 16#64) t = r (.GPR 20#5) s
  second : read_mem_bytes 8 (bodySP s + 24#64) t = r (.GPR 19#5) s

theorem prologue_saved (s : ArmState) (low : 32 ≤ (r (.GPR 31#5) s).toNat) :
    Saved s (prologue s) := by
  refine ⟨prologue_sp s, ?_, ?_, ?_⟩
  all_goals
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (prologue_memory s))]
    simp only [savedMemory]
    simp (disch := (simp only [bodySP]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

def returnOps (result : Bool) : List Op :=
  if result then [.p188, .p192, .p196, .p200] else [.p172, .p176, .p180, .p184]

@[irreducible] def finish (s : ArmState) (result : Bool) : ArmState :=
  block (returnOps result) s

theorem finish_run (s : ArmState) (base : BitVec 64) (result : Bool)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + if result then 188#64 else 172#64) :
    run 4 s = finish s result := by
  rw [finish]
  have pcs : PCs base (returnOps result) s := by
    change r .PC s = _ at pc
    cases result <;> simp [PCs, returnOps, Op.row, Op.effect, next, put, loadPair,
      restore, state_simp_rules, pc, BitVec.add_assoc]
  have executed := run_block (returnOps result) s base code error aligned pcs
  cases result <;> exact executed

@[simp] theorem finish_memory (s : ArmState) (result : Bool) :
    (finish s result).mem = s.mem := by
  cases result <;> simp [finish, returnOps, block, Op.effect, next, put,
    loadPair, restore, state_simp_rules]

@[simp] theorem finish_result (s : ArmState) (result : Bool) :
    r (.GPR 0#5) (finish s result) = if result then 1#64 else 0#64 := by
  cases result <;> simp [finish, returnOps, block, Op.effect, next, put,
    loadPair, restore, state_simp_rules]

theorem finish_saved (s t : ArmState) (result : Bool) (saved : Saved s t) :
    read_pc (finish t result) = r (.GPR 30#5) s ∧
    r (.GPR 31#5) (finish t result) = r (.GPR 31#5) s ∧
    r (.GPR 30#5) (finish t result) = r (.GPR 30#5) s ∧
    r (.GPR 20#5) (finish t result) = r (.GPR 20#5) s ∧
    r (.GPR 19#5) (finish t result) = r (.GPR 19#5) s := by
  cases result <;> simp [finish, returnOps, block, Op.effect, next, put,
    loadPair, restore, state_simp_rules, saved.sp, saved.link, saved.first,
    saved.second, BitVec.add_assoc]
  all_goals
    simp only [bodySP]
    bv_omega

end SszArm.Codec.Fixed.IsFixed
