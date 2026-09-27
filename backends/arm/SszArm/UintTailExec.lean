import SszArm.UintImpl
import SszArm.BoolTails
import SszArm.BoolActivation
import SszArm.MemcpyProofs

namespace SszArm.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Only the extra instructions in the UInt tails; shared lowering instructions
use the already proved Boolean opcode semantics. -/
inductive Op where
  | shared (op : StoreOp)
  | pairNat | valueTag | successJump
  | add64 | storeExpected | storeCount | reasonScope | storeActual
  | zeroVector | errorTag | saveOut | add8 | storeErrorTag
  | out24 | source64 | count48 | zeroPair144 | zero176
  | loadPair144 | load176 | storePair64 | store96 | callMemcpy
  | reasonScratch | storeTagOut | storeReasonOut | returnJump
  deriving DecidableEq

def Op.word : Op → BitVec 32
  | .shared op => op.word
  | .pairNat => 0xa901a80c#32
  | .valueTag => 0x39004008#32
  | .successJump => 0x14000008#32
  | .add64 => 0x91010129#32
  | .storeExpected => 0xf9000528#32
  | .storeCount => 0xf9001009#32
  | .reasonScope => 0x52800068#32
  | .storeActual => 0xf9000523#32
  | .zeroVector => 0x6f00e400#32
  | .errorTag => 0x52800033#32
  | .saveOut => 0xaa0003f4#32
  | .add8 => 0x91002129#32
  | .storeErrorTag => 0xf9000133#32
  | .out24 => 0x91006000#32
  | .source64 => 0x910103e1#32
  | .count48 => 0x52800602#32
  | .zeroPair144 => 0xad0483e0#32
  | .zero176 => 0x3d802fe0#32
  | .loadPair144 => 0xad4483e1#32
  | .load176 => 0x3dc02fe2#32
  | .storePair64 => 0xad0203e1#32
  | .store96 => 0x3d801be2#32
  | .callMemcpy => 0x94006101#32
  | .reasonScratch => 0x52900008#32
  | .storeTagOut => 0xf9000293#32
  | .storeReasonOut => 0xb9004a88#32
  | .returnJump => 0x17ffffd0#32

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64) (w (.GPR reg) value s)

def Op.effect : Op → ArmState → ArmState
  | .shared op, s => op.effect s
  | .pairNat, s => next (write_mem_bytes 16 (r (.GPR 0) s + 24#64)
      (r (.GPR 10) s ++ r (.GPR 12) s) s)
  | .valueTag, s => next (write_mem_bytes 1 (r (.GPR 0) s + 16#64)
      ((r (.GPR 8) s).setWidth 8) s)
  | .successJump, s => w .PC (read_pc s + 32#64) s
  | .add64, s => put 9 (r (.GPR 9) s + 64#64) s
  | .storeExpected, s => next (write_mem_bytes 8 (r (.GPR 9) s + 8#64) (r (.GPR 8) s) s)
  | .storeCount, s => next (write_mem_bytes 8 (r (.GPR 0) s + 32#64) (r (.GPR 9) s) s)
  | .reasonScope, s => put 8 3#64 s
  | .storeActual, s => next (write_mem_bytes 8 (r (.GPR 9) s + 8#64) (r (.GPR 3) s) s)
  | .zeroVector, s => next (w (.SFP 0) 0#128 s)
  | .errorTag, s => put 19 1#64 s
  | .saveOut, s => put 20 (r (.GPR 0) s) s
  | .add8, s => put 9 (r (.GPR 9) s + 8#64) s
  | .storeErrorTag, s => next (write_mem_bytes 8 (r (.GPR 9) s) (r (.GPR 19) s) s)
  | .out24, s => put 0 (r (.GPR 0) s + 24#64) s
  | .source64, s => put 1 (r (.GPR 31) s + 64#64) s
  | .count48, s => put 2 48#64 s
  | .zeroPair144, s => next (write_mem_bytes 32 (r (.GPR 31) s + 144#64)
      (r (.SFP 0) s ++ r (.SFP 0) s) s)
  | .zero176, s => next (write_mem_bytes 16 (r (.GPR 31) s + 176#64) (r (.SFP 0) s) s)
  | .loadPair144, s =>
      let q := read_mem_bytes 32 (r (.GPR 31) s + 144#64) s
      next (w (.SFP 0) (q.extractLsb' 128 128) (w (.SFP 1) (q.extractLsb' 0 128) s))
  | .load176, s => next (w (.SFP 2) (read_mem_bytes 16 (r (.GPR 31) s + 176#64) s) s)
  | .storePair64, s => next (write_mem_bytes 32 (r (.GPR 31) s + 64#64)
      (r (.SFP 0) s ++ r (.SFP 1) s) s)
  | .store96, s => next (write_mem_bytes 16 (r (.GPR 31) s + 96#64) (r (.SFP 2) s) s)
  | .callMemcpy, s => w .PC (read_pc s + 99332#64) (w (.GPR 30) (read_pc s + 4#64) s)
  | .reasonScratch, s => put 8 32768#64 s
  | .storeTagOut, s => next (write_mem_bytes 8 (r (.GPR 20) s) (r (.GPR 19) s) s)
  | .storeReasonOut, s => next (write_mem_bytes 4 (r (.GPR 20) s + 72#64)
      ((r (.GPR 8) s).setWidth 32) s)
  | .returnJump, s => w .PC (read_pc s - 192#64) s

theorem step_word (s : ArmState) (op : Op)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some op.word) :
    stepi s = op.effect s := by
  cases op
  case shared op => exact BoolCodec.step_word s op he ha hf
  all_goals
    simp only [Op.word] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, ha, BitVec.sub_eq_add_neg]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem effect_program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules, StoreOp.effect_program]

@[simp] theorem effect_error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op
  case shared op => exact StoreOp.effect_error op s
  all_goals simp [Op.effect, next, put, state_simp_rules]

theorem effect_aligned (op : Op) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules, ha]
  exact StoreOp.effect_aligned _ _ ha

def block : List Op → ArmState → ArmState
  | [], s => s
  | op :: ops, s => block ops (op.effect s)

def Follows (base : BitVec 64) : List (Nat × Op) → ArmState → Prop
  | [], _ => True
  | (pc, op) :: ops, s => (pc, op.word) ∈ program ∧
      read_pc s = base + BitVec.ofNat 64 pc ∧ Follows base ops (op.effect s)

theorem follows_run (base : BitVec 64) (ops : List (Nat × Op)) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) :
    run ops.length s = block (ops.map Prod.snd) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons row ops ih =>
    rcases row with ⟨pc, op⟩
    rcases hf with ⟨hm, hp, hf⟩
    have fetch : s.program.find? (read_pc s) = some op.word := by
      rw [hp]; exact hc _ hm
    rw [List.length_cons, run_opener_general, step_word s op he ha fetch]
    exact ih _ (by simpa only [CodeAt, effect_program] using hc)
      (by simpa only [effect_error] using he) (effect_aligned op s ha) hf

@[simp] theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (effect_program op s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (effect_error op s)

theorem block_aligned (ops : List Op) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (block ops s) := by
  induction ops generalizing s with
  | nil => exact ha
  | cons op ops ih => exact ih _ (effect_aligned op s ha)

def successOps : List (Nat × Op) :=
  [(4460, .shared .movW8_1), (4464, .pairNat), (4468, .successJump), (4500, .valueTag)]

def scopeOps : List (Nat × Op) :=
  [(4544, .shared .subSp16), (4548, .shared .strX9Sp), (4552, .shared .strX10Sp8),
   (4556, .shared .addX9X0_0), (4560, .add64), (4564, .shared .movX10_0),
   (4568, .shared .strX10X9), (4572, .shared .ldrX10Sp8), (4576, .shared .ldrX9Sp),
   (4580, .shared .addSp16), (4584, .shared .subSp16), (4588, .shared .strX9Sp),
   (4592, .shared .strX10Sp8), (4596, .shared .addX9X0_0), (4600, .shared .addX9X9_16),
   (4604, .shared .movX10_0), (4608, .shared .strX10X9), (4612, .storeExpected),
   (4616, .shared .ldrX10Sp8), (4620, .shared .ldrX9Sp), (4624, .shared .addSp16),
   (4628, .storeCount), (4632, .reasonScope), (4636, .shared .subSp16),
   (4640, .shared .strX9Sp), (4644, .shared .strX10Sp8), (4648, .shared .addX9X0_0),
   (4652, .shared .addX9X9_40), (4656, .shared .movX10_0), (4660, .shared .strX10X9),
   (4664, .storeActual), (4668, .shared .ldrX10Sp8), (4672, .shared .ldrX9Sp),
   (4676, .shared .addSp16), (4680, .shared .subSp16), (4684, .shared .strX9Sp),
   (4688, .shared .strX10Sp8), (4692, .shared .addX9X0_0), (4696, .shared .addX9X9_56),
   (4700, .shared .movX10_0), (4704, .shared .strX10X9), (4708, .shared .ldrX10Sp8),
   (4712, .shared .ldrX9Sp), (4716, .shared .addSp16)]

def failureOps : List (Nat × Op) :=
  [(4816, .zeroVector), (4820, .errorTag), (4824, .saveOut),
   (4828, .shared .subSp16), (4832, .shared .strX9Sp), (4836, .shared .strX10Sp8),
   (4840, .shared .addX9X0_0), (4844, .add8), (4848, .storeErrorTag),
   (4852, .shared .movX10_0), (4856, .shared .strX10X9_8),
   (4860, .shared .ldrX10Sp8), (4864, .shared .ldrX9Sp), (4868, .shared .addSp16),
   (4872, .out24), (4876, .source64), (4880, .count48), (4884, .zeroPair144),
   (4888, .zero176), (4892, .loadPair144), (4896, .load176),
   (4900, .storePair64), (4904, .store96), (4908, .callMemcpy)]

def failureReturnOps : List (Nat × Op) :=
  [(4912, .reasonScratch), (4916, .storeTagOut), (4920, .storeReasonOut), (4924, .returnJump)]

macro "tail_follow" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    [Follows, successOps, scopeOps, failureOps, failureReturnOps, Op.word,
     Op.effect, StoreOp.effect, next, put, state_simp_rules, BitVec.add_assoc,
     BitVec.sub_eq_add_neg, program, bodyProgram, memcpyProgram, memcpyOffset])

theorem success_block (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4460#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 4 s = block (successOps.map Prod.snd) s := by
  apply follows_run base successOps s hc he ha
  have hpc : r .PC s = base + 4460#64 := hp
  tail_follow <;> simp [hpc, BitVec.add_assoc]

theorem scope_block (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4544#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 44 s = block (scopeOps.map Prod.snd) s := by
  apply follows_run base scopeOps s hc he ha
  have hpc : r .PC s = base + 4544#64 := hp
  tail_follow <;> simp [hpc, BitVec.add_assoc]

theorem failure_block (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4816#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 24 s = block (failureOps.map Prod.snd) s := by
  apply follows_run base failureOps s hc he ha
  have hpc : r .PC s = base + 4816#64 := hp
  tail_follow <;> simp [hpc, BitVec.add_assoc]

theorem failure_return_block (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4912#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 4 s = block (failureReturnOps.map Prod.snd) s := by
  apply follows_run base failureReturnOps s hc he ha
  have hpc : r .PC s = base + 4912#64 := hp
  tail_follow <;> simp [hpc, BitVec.add_assoc]

end SszArm.UintCodec.Tail
