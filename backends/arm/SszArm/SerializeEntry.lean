import SszArm.SerializeExec
import SszArm.SerializeGeometry
import SszArm.UintResultMemory

namespace SszArm.Serialize

open Delimited (MemoryFrame)

private def prologueOps : List Op := [.p0, .p4, .p8, .p12]

def savedRegisters : List (BitVec 5 × Nat) :=
  [(30#5, 96), (23#5, 104), (22#5, 112), (21#5, 120), (20#5, 128), (19#5, 136)]

@[irreducible] def prologue (base : BitVec 64) (s : ArmState) : ArmState :=
  block base prologueOps s

def savedMemory (s : ArmState) : ArmState :=
  let sp := (Args.ofEntry s).bodySP
  write_mem_bytes 16 (sp + 128#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
  (write_mem_bytes 16 (sp + 112#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
  (write_mem_bytes 16 (sp + 96#64) (r (.GPR 23#5) s ++ r (.GPR 30#5) s) s))

@[simp] theorem prologue_sp (base : BitVec 64) (s : ArmState) :
    r (.GPR 31#5) (prologue base s) = (Args.ofEntry s).bodySP := by
  simp [prologue, prologueOps, block, Op.effect, put, next,
    Args.ofEntry, Args.bodySP, state_simp_rules]

@[simp] theorem prologue_register (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) (different : reg ≠ 31#5) :
    r (.GPR reg) (prologue base s) = r (.GPR reg) s := by
  simp [prologue, prologueOps, block, Op.effect, put, next, different, state_simp_rules]

@[simp] theorem prologue_pc (base : BitVec 64) (s : ArmState) :
    read_pc (prologue base s) = read_pc s + 16#64 := by
  simp [prologue, prologueOps, block, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]

@[simp] theorem prologue_program (base : BitVec 64) (s : ArmState) :
    (prologue base s).program = s.program := by
  simp [prologue, prologueOps]

@[simp] theorem prologue_error (base : BitVec 64) (s : ArmState) :
    read_err (prologue base s) = read_err s := by
  simp [prologue, prologueOps]

@[simp] theorem prologue_memory (base : BitVec 64) (s : ArmState) :
    (prologue base s).mem = (savedMemory s).mem := by
  simp [prologue, prologueOps, block, Op.effect, put, next,
    savedMemory, Args.ofEntry, Args.bodySP, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem prologue_vector (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (prologue base s) = r (.SFP reg) s := by
  simp [prologue, prologueOps]

theorem prologue_aligned (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (prologue base s) := by
  rw [prologue]
  exact block_aligned base prologueOps s aligned

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 4 s = prologue base s := by
  rw [prologue]
  apply block_run base prologueOps s code error aligned
  change r .PC s = base at pc
  simp [prologueOps, Follows, Op.row, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

theorem prologue_frame (s : ArmState) (base : BitVec 64)
    (low : 432 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (saveWrites (Args.ofEntry s)) s (prologue base s) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 48, 48)
    (by simp [saveWrites, Args.ofEntry])
  simp only [Prod.fst, Prod.snd] at apart
  rw [prologue_memory]
  simp only [savedMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)
    (by simp only [Args.bodySP, Args.ofEntry]; bv_omega)]

theorem prologue_saved (s : ArmState) (base : BitVec 64)
    (low : 432 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (displacement : Nat) (member : (reg, displacement) ∈ savedRegisters) :
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 displacement) (prologue base s) =
      r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (prologue_memory base s))]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [savedMemory]
    simp (disch := (simp only [Args.bodySP, Args.ofEntry]; bv_omega)) only
      [UintCodec.Tail.write_pair_words, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

private def callOps : List Op :=
  [.p16, .p20, .p24, .p28, .p32, .p36, .p40, .p44, .p48]

@[irreducible] def measurementEntry (base : BitVec 64) (s : ArmState) : ArmState :=
  block base callOps (prologue base s)

structure Registers (t : ArmState) (args : Args) : Prop where
  result : r (.GPR 19#5) t = args.result
  output : r (.GPR 20#5) t = args.output
  value : r (.GPR 21#5) t = args.value
  descriptor : r (.GPR 22#5) t = args.descriptor
  capacity : r (.GPR 23#5) t = args.capacity
  stack : r (.GPR 31#5) t = args.bodySP

@[simp] theorem measurementEntry_program (base : BitVec 64) (s : ArmState) :
    (measurementEntry base s).program = s.program := by
  simp [measurementEntry]

@[simp] theorem measurementEntry_error (base : BitVec 64) (s : ArmState) :
    read_err (measurementEntry base s) = read_err s := by
  simp [measurementEntry]

@[simp] theorem measurementEntry_memory (base : BitVec 64) (s : ArmState) :
    (measurementEntry base s).mem = (prologue base s).mem := by
  simp [measurementEntry, callOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem measurementEntry_pc (base : BitVec 64) (s : ArmState) :
    read_pc (measurementEntry base s) = base + measureOffset := by
  simp [measurementEntry, callOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem measurementEntry_lr (base : BitVec 64) (s : ArmState) :
    r (.GPR 30#5) (measurementEntry base s) = base + 52#64 := by
  simp [measurementEntry, callOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem measurementEntry_args (base : BitVec 64) (s : ArmState) :
    Measure.Args.ofEntry (measurementEntry base s) = (Args.ofEntry s).measure := by
  simp [measurementEntry, callOps, block, Op.effect, put, next,
    Measure.Args.ofEntry, Args.ofEntry, Args.measure, Args.plan,
    state_simp_rules, prologue_register, prologue_sp]

@[simp] theorem measurementEntry_registers (base : BitVec 64) (s : ArmState) :
    Registers (measurementEntry base s) (Args.ofEntry s) := by
  constructor <;>
    simp [measurementEntry, callOps, block, Op.effect, put, next,
      Args.ofEntry, state_simp_rules, prologue_register, prologue_sp]

theorem measurementEntry_untouched (base : BitVec 64) (s : ArmState) (reg : BitVec 5)
    (low : 18 ≤ reg.toNat) (high : reg.toNat ≤ 29)
    (outside : reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5]) :
    r (.GPR reg) (measurementEntry base s) = r (.GPR reg) s := by
  have different0 : reg ≠ 0#5 := by bv_omega
  have different3 : reg ≠ 3#5 := by bv_omega
  have different4 : reg ≠ 4#5 := by bv_omega
  have different30 : reg ≠ 30#5 := by bv_omega
  have different31 : reg ≠ 31#5 := by bv_omega
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp [measurementEntry, callOps, block, Op.effect, put, next, state_simp_rules,
    different0, different3, different4, different30, different31,
    outside.1, outside.2.1, outside.2.2.1, outside.2.2.2.1, outside.2.2.2.2]

@[simp] theorem measurementEntry_vector (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (measurementEntry base s) = r (.SFP reg) s := by
  simp [measurementEntry]

theorem measurementEntry_aligned (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (measurementEntry base s) := by
  rw [measurementEntry]
  exact block_aligned base callOps _ (prologue_aligned base s aligned)

theorem measurementEntry_frame (s : ArmState) (base : BitVec 64)
    (low : 432 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (saveWrites (Args.ofEntry s)) s (measurementEntry base s) := by
  intro address outside
  rw [measurementEntry_memory]
  exact prologue_frame s base low address outside

theorem measurementEntry_saved (s : ArmState) (base : BitVec 64)
    (low : 432 ≤ (r (.GPR 31#5) s).toNat)
    (reg : BitVec 5) (displacement : Nat) (member : (reg, displacement) ∈ savedRegisters) :
    read_mem_bytes 8 ((Args.ofEntry s).bodySP + BitVec.ofNat 64 displacement)
      (measurementEntry base s) = r (.GPR reg) s := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (measurementEntry_memory base s))]
  exact prologue_saved s base low reg displacement member

theorem measurementEntry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 13 s = measurementEntry base s := by
  have before : read_pc (prologue base s) = base + 16#64 := by rw [prologue_pc, pc]
  change run (4 + 9) s = _
  rw [run_plus, prologue_run s base code error aligned pc, measurementEntry]
  apply block_run base callOps _ (code.congr (prologue_program base s))
    ((prologue_error base s).trans error) (prologue_aligned base s aligned)
  change r .PC (prologue base s) = base + 16#64 at before
  simp [callOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
    before, BitVec.add_assoc]

end SszArm.Serialize
