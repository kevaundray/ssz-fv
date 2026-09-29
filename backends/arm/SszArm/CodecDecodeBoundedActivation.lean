import SszArm.CodecDecodeBoundedContract
import SszArm.BoolActivation
import SszArm.UintResultMemory

namespace SszArm.Codec.Decode.Bounded

open Delimited (MemoryFrame)

def bodySP (s : ArmState) : BitVec 64 := r (.GPR 31#5) s - 48#64

def prologueOps : List Op := [.p0, .p4, .p8, .p12]

@[irreducible] def prologue (s : ArmState) (base : BitVec 64) : ArmState :=
  block base prologueOps s

def savedRegisters : List (BitVec 5 × Nat) :=
  [(30#5, 0), (22#5, 16), (21#5, 24), (20#5, 32), (19#5, 40)]

def savedMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 32#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
    (write_mem_bytes 16 (bodySP s + 16#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
      (write_mem_bytes 8 (bodySP s) (r (.GPR 30#5) s) s))

@[simp] theorem prologue_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (prologue s base) = bodySP s := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, bodySP, state_simp_rules]

@[simp] theorem prologue_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (different : reg ≠ 31#5) : r (.GPR reg) (prologue s base) = r (.GPR reg) s := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, different, state_simp_rules]

@[simp] theorem prologue_pc (s : ArmState) (base : BitVec 64) :
    read_pc (prologue s base) = read_pc s + 16#64 := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (s : ArmState) (base : BitVec 64) :
    (prologue s base).program = s.program := by
  simp [prologue, prologueOps, block]

@[simp] theorem prologue_error (s : ArmState) (base : BitVec 64) :
    read_err (prologue s base) = read_err s := by
  simp [prologue, prologueOps, block]

@[simp] theorem prologue_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (prologue s base) = r (.SFP reg) s := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, state_simp_rules]

@[simp] theorem prologue_memory (s : ArmState) (base : BitVec 64) :
    (prologue s base).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, block, Op.effect, put, next, save, savedMemory, bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem prologue_aligned (s : ArmState) (base : BitVec 64) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (prologue s base) :=
  CheckSPAlignment_of_r_sp_aligned (prologue_sp s base)
    (aligned_sub48 _ (BoolCodec.stack_aligned s aligned))

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 4 s = prologue s base := by
  have follows : Follows base prologueOps s := by
    change r .PC s = base at pc
    simp [Follows, prologueOps, Op.row, Op.effect, put, next, save,
      state_simp_rules, pc, BitVec.add_assoc]
  simpa only [prologue, prologueOps, List.length_cons, List.length_nil] using
    block_run base prologueOps s code error aligned follows

theorem prologue_frame (s : ArmState) (base : BitVec 64)
    (low : 64 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (stackWrites s) s (prologue s base) := by
  intro address outside
  have link := outside ((r (.GPR 31#5) s).toNat - 48, 8) (by simp [stackWrites])
  have saved := outside ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [stackWrites])
  simp only [Prod.fst, Prod.snd] at link saved
  rw [prologue_memory]
  simp only [savedMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address
      (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address
      (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address
    (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)

theorem prologue_saved (s : ArmState) (base : BitVec 64)
    (low : 64 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (prologue s base) = r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (prologue_memory s base))]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [savedMemory]
    simp (disch := (simp only [bodySP]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BitVec.ofNat_eq_ofNat, BitVec.add_zero,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

end SszArm.Codec.Decode.Bounded
