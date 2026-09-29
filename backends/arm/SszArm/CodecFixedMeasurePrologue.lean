import SszArm.CodecFixedMeasureAlignment
import SszArm.CodecFixedMeasureContract
import SszArm.UintResultMemory

namespace SszArm.Codec.Fixed.MeasureFixed

open Dispatch.Block (next put save)
open Delimited (MemoryFrame)

def prologueOps : List Op := [.entry .p0, .entry .p4, .entry .p8, .entry .p12,
  .entry .p16, .entry .p20]

@[irreducible] def prologue (s : ArmState) : ArmState := block prologueOps s

def savedRegisters : List (BitVec 5 × Nat) :=
  [(30#5, 80), (26#5, 96), (25#5, 104), (24#5, 112), (23#5, 120),
    (22#5, 128), (21#5, 136), (20#5, 144), (19#5, 152)]

/-- The single LR store and four paired stores of the linked prologue. -/
def savedMemory (s : ArmState) : ArmState :=
  let sp := (Args.ofEntry s).bodySP
  write_mem_bytes 16 (sp + 144#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
  (write_mem_bytes 16 (sp + 128#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
  (write_mem_bytes 16 (sp + 112#64) (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
  (write_mem_bytes 16 (sp + 96#64) (r (.GPR 25#5) s ++ r (.GPR 26#5) s)
  (write_mem_bytes 8 (sp + 80#64) (r (.GPR 30#5) s) s))))

@[simp] theorem prologue_sp (s : ArmState) :
    r (.GPR 31#5) (prologue s) = (Args.ofEntry s).bodySP := by
  simp [prologue, prologueOps, block, Op.effect, Entry.Op.effect, next, put, save,
    Args.ofEntry, Args.bodySP, state_simp_rules]

@[simp] theorem prologue_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 31#5) :
    r (.GPR reg) (prologue s) = r (.GPR reg) s := by
  simp [prologue, prologueOps, block, Op.effect, Entry.Op.effect, next, put, save,
    different, state_simp_rules]

@[simp] theorem prologue_pc (s : ArmState) : read_pc (prologue s) = read_pc s + 24#64 := by
  simp [prologue, prologueOps, block, Op.effect, Entry.Op.effect, next, put, save,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (s : ArmState) : (prologue s).program = s.program := by
  exact block_program prologueOps s

@[simp] theorem prologue_error (s : ArmState) : read_err (prologue s) = read_err s := by
  exact block_error prologueOps s

@[simp] theorem prologue_memory (s : ArmState) : (prologue s).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, block, Op.effect, Entry.Op.effect, next, put, save,
    savedMemory, Args.ofEntry, Args.bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem prologue_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (prologue s) = r (.SFP reg) s := by
  simp [prologue, prologueOps, block, Op.effect, Entry.Op.effect, next, put, save, state_simp_rules]

theorem prologue_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (prologue s) := block_aligned prologueOps s aligned

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) : run 6 s = prologue s := by
  have pcs : PCs base prologueOps s := by
    change r .PC s = base at pc
    simp [PCs, prologueOps, Op.row, Entry.Op.row, Op.effect, Entry.Op.effect,
      put, next, save, state_simp_rules, pc, BitVec.add_assoc]
  exact run_block prologueOps s base code error aligned pcs

theorem prologue_frame (s : ArmState) (low : 160 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (Stack.envelope (r (.GPR 31#5) s).toNat 160) s (prologue s) := by
  intro a outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 160, 160) (by simp [Stack.envelope])
  simp only [Prod.fst, Prod.snd] at apart
  rw [prologue_memory]
  simp only [savedMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ a
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ a
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)]

theorem prologue_saved (s : ArmState) (low : 160 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 offset) (prologue s) =
      r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (prologue_memory s))]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [savedMemory]
    simp (disch := (simp only [Args.bodySP, Args.ofEntry]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

structure Saved (source current : ArmState) : Prop where
  sp : r (.GPR 31#5) current = (Args.ofEntry source).bodySP
  slots : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 ((Args.ofEntry source).bodySP + BitVec.ofNat 64 offset) current =
      r (.GPR reg) source

theorem prologue_saved_state (s : ArmState) (low : 160 ≤ (r (.GPR 31#5) s).toNat) :
    Saved s (prologue s) := ⟨prologue_sp s, prologue_saved s low⟩

end SszArm.Codec.Fixed.MeasureFixed
