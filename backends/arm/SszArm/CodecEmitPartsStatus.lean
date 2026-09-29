import SszArm.CodecEmitPartsOps

namespace SszArm.Codec.Emit.Parts

open SszArm.Emit.Activation (next put)
open Delimited (Span Protected MemoryFrame)

inductive FinishKind where
  | sequential | table
  deriving DecidableEq

def FinishKind.result : FinishKind → BitVec 5
  | .sequential => 26 | .table => 8

def FinishKind.size : FinishKind → BitVec 5
  | .sequential => 24 | .table => 25

def FinishKind.start : FinishKind → Nat
  | .sequential => 740 | .table => 796

def FinishKind.ops : FinishKind → List Op
  | .sequential =>
      [.p740, .p744, .p748, .p752, .p756, .p760, .p764, .p768, .p772, .p776, .p780, .p784]
  | .table =>
      [.p796, .p800, .p804, .p808, .p812, .p816, .p820, .p824, .p828, .p832, .p836, .p840]

@[irreducible] def finished (kind : FinishKind) (s : ArmState) : ArmState := block kind.ops s

def finishMemory (kind : FinishKind) (s : ArmState) : ArmState :=
  write_mem_bytes 4 (r (.GPR kind.result) s + 64#64) 0#32
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (r (.GPR 10#5) s)
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s)
        (write_mem_bytes 8 (r (.GPR kind.result) s) (r (.GPR kind.size) s) s)))

def finishWrites (kind : FinishKind) (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16),
   ((r (.GPR kind.result) s).toNat, 8), ((r (.GPR kind.result) s).toNat + 64, 4)]

@[simp] theorem finished_program (kind : FinishKind) (s : ArmState) :
    (finished kind s).program = s.program := by simp [finished]

@[simp] theorem finished_error (kind : FinishKind) (s : ArmState) :
    read_err (finished kind s) = read_err s := by simp [finished]

@[simp] theorem finished_sp (kind : FinishKind) (s : ArmState) :
    r (.GPR 31#5) (finished kind s) = r (.GPR 31#5) s := by
  cases kind <;> simp [finished, FinishKind.ops, block, Op.effect, put, next,
    state_simp_rules, BitVec.sub_add_cancel]

@[simp] theorem finished_register (kind : FinishKind) (s : ArmState) (reg : BitVec 5)
    (not9 : reg ≠ 9#5) (not10 : reg ≠ 10#5) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (finished kind s) = r (.GPR reg) s := by
  cases kind <;> simp [finished, FinishKind.ops, block, Op.effect, put, next,
    state_simp_rules, not9, not10, notSP]

@[simp] theorem finished_vector (kind : FinishKind) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (finished kind s) = r (.SFP reg) s := by simp [finished]

@[simp] theorem finished_memory (kind : FinishKind) (s : ArmState) :
    (finished kind s).mem = (finishMemory kind s).mem := by
  cases kind <;>
    simp [finished, FinishKind.ops, FinishKind.result, FinishKind.size,
      block, Op.effect, put, next, finishMemory, state_simp_rules] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem finished_aligned (kind : FinishKind) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (finished kind s) := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, finished_sp] using aligned

theorem finished_pc (kind : FinishKind) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.start) :
    read_pc (finished kind s) = base + 1088#64 := by
  change r .PC s = _ at pc
  cases kind <;> simp [finished, FinishKind.ops, FinishKind.start,
    block, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

theorem finished_run (kind : FinishKind) (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 kind.start) :
    run 12 s = finished kind s := by
  have lower : Aligned (r (.GPR 31#5) s - 16#64) 4 := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr,
      Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  have follows : Follows base kind.ops s := by
    change r .PC s = _ at pc
    cases kind <;>
      simp (config := {decide := true}) [Follows, FinishKind.ops, FinishKind.start,
        Op.row, Op.effect, put, next, state_simp_rules, CheckSPAlignment, read_gpr,
        BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned lower ⊢ <;>
      exact ⟨aligned, lower, by simpa only [BitVec.sub_add_cancel] using aligned⟩
  have execution := runs kind.ops s base code error follows
  rw [finished]
  cases kind <;> exact execution

theorem finished_frame (kind : FinishKind) (s : ArmState)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (bound : (r (.GPR kind.result) s).toNat + 68 ≤ 2 ^ 64) :
    MemoryFrame (finishWrites kind s) s (finished kind s) := by
  intro address outside
  have scratch := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [finishWrites])
  have length := outside ((r (.GPR kind.result) s).toNat, 8) (by simp [finishWrites])
  have status := outside ((r (.GPR kind.result) s).toNat + 64, 4) (by simp [finishWrites])
  simp only [Prod.fst, Prod.snd] at scratch length status
  rw [finished_memory]
  simp only [finishMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 4 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)

theorem finished_status (kind : FinishKind) (s : ArmState)
    (bound : (r (.GPR kind.result) s).toNat + 68 ≤ 2 ^ 64) :
    read_mem_bytes 4 (r (.GPR kind.result) s + 64#64) (finished kind s) = 0#32 := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (finished_memory kind s))]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 4 _ _ (by bv_omega)

theorem finished_length (kind : FinishKind) (s : ArmState)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (bound : (r (.GPR kind.result) s).toNat + 68 ≤ 2 ^ 64)
    (separate : Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
      (r (.GPR kind.result) s).toNat 68) :
    read_mem_bytes 8 (r (.GPR kind.result) s) (finished kind s) = r (.GPR kind.size) s := by
  rcases separate with impossible | separate
  · omega
  have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  simp only [Prod.fst, Prod.snd] at apart
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (finished_memory kind s))]
  simp only [finishMemory]
  simp (disch := bv_omega) only
    [BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

end SszArm.Codec.Emit.Parts
