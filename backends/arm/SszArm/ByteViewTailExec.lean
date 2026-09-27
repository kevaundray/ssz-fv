import SszArm.ByteViewImpl
import SszArm.UintTails

namespace SszArm.ByteView.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

inductive Op where
  | shared (op : UintCodec.Tail.Op)
  | bytesTag | pairBytes | save10 | save11 | out10 | add32 | storeCount
  | zero11 | storeZero11 | restore11 | restore10 | actual | errorJump
  deriving DecidableEq

def Op.word : Op → BitVec 32
  | .shared op => op.word
  | .bytesTag => 0x52800048#32
  | .pairBytes => 0xa9018c02#32
  | .save10 => 0xf90003ea#32
  | .save11 => 0xf90007eb#32
  | .out10 => 0x9100000a#32
  | .add32 => 0x9100814a#32
  | .storeCount => 0xf9000149#32
  | .zero11 => 0xd280000b#32
  | .storeZero11 => 0xf900054b#32
  | .restore11 => 0xf94007eb#32
  | .restore10 => 0xf94003ea#32
  | .actual => 0xf9001803#32
  | .errorJump => 0x140000fa#32

def Op.effect : Op → ArmState → ArmState
  | .shared op, s => op.effect s
  | .bytesTag, s => UintCodec.Tail.put 8 2#64 s
  | .pairBytes, s => UintCodec.Tail.next (write_mem_bytes 16 (r (.GPR 0) s + 24#64)
      (r (.GPR 3) s ++ r (.GPR 2) s) s)
  | .save10, s => UintCodec.Tail.next (write_mem_bytes 8 (r (.GPR 31) s) (r (.GPR 10) s) s)
  | .save11, s => UintCodec.Tail.next (write_mem_bytes 8 (r (.GPR 31) s + 8#64) (r (.GPR 11) s) s)
  | .out10, s => UintCodec.Tail.put 10 (r (.GPR 0) s) s
  | .add32, s => UintCodec.Tail.put 10 (r (.GPR 10) s + 32#64) s
  | .storeCount, s => UintCodec.Tail.next (write_mem_bytes 8 (r (.GPR 10) s) (r (.GPR 9) s) s)
  | .zero11, s => UintCodec.Tail.put 11 0#64 s
  | .storeZero11, s => UintCodec.Tail.next (write_mem_bytes 8 (r (.GPR 10) s + 8#64) (r (.GPR 11) s) s)
  | .restore11, s => UintCodec.Tail.put 11 (read_mem_bytes 8 (r (.GPR 31) s + 8#64) s) s
  | .restore10, s => UintCodec.Tail.put 10 (read_mem_bytes 8 (r (.GPR 31) s) s) s
  | .actual, s => UintCodec.Tail.next (write_mem_bytes 8 (r (.GPR 0) s + 48#64) (r (.GPR 3) s) s)
  | .errorJump, s => w .PC (read_pc s + 1000#64) s

theorem step_word (s : ArmState) (op : Op)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some op.word) : stepi s = op.effect s := by
  cases op
  case shared op => exact UintCodec.Tail.step_word s op he ha hf
  all_goals
    simp only [Op.word] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, UintCodec.Tail.next, UintCodec.Tail.put, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, ha]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem effect_program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, UintCodec.Tail.next, UintCodec.Tail.put, state_simp_rules]

@[simp] theorem effect_error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op
  case shared op => exact UintCodec.Tail.effect_error op s
  all_goals simp [Op.effect, UintCodec.Tail.next, UintCodec.Tail.put, state_simp_rules]

theorem effect_aligned (op : Op) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  cases op
  case shared op => exact UintCodec.Tail.effect_aligned op s ha
  all_goals simp [Op.effect, UintCodec.Tail.next, UintCodec.Tail.put, state_simp_rules, ha]

def block : List Op → ArmState → ArmState
  | [], s => s
  | op :: ops, s => block ops (op.effect s)

def Follows (base : BitVec 64) : List (Nat × Op) → ArmState → Prop
  | [], _ => True
  | (pc, op) :: ops, s => (pc, op.word) ∈ program ∧
      read_pc s = base + BitVec.ofNat 64 pc ∧ Follows base ops (op.effect s)

theorem follows_run (base : BitVec 64) (ops : List (Nat × Op)) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) : run ops.length s = block (ops.map Prod.snd) s := by
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
  [(4492, .bytesTag), (4496, .pairBytes), (4500, .shared .valueTag)]

def limitOps : List (Nat × Op) :=
  [(3576, .shared (.shared .subSp16)), (3580, .shared (.shared .strX9Sp)),
   (3584, .shared (.shared .strX10Sp8)), (3588, .shared (.shared .addX9X0_0)),
   (3592, .shared (.shared .addX9X9_56)), (3596, .shared (.shared .movX10_0)),
   (3600, .shared (.shared .strX10X9)), (3604, .shared (.shared .movX10_0)),
   (3608, .shared (.shared .strX10X9_8)), (3612, .shared (.shared .ldrX10Sp8)),
   (3616, .shared (.shared .ldrX9Sp)), (3620, .shared (.shared .addSp16)),
   (3624, .shared (.shared .subSp16)), (3628, .shared (.shared .strX9Sp)),
   (3632, .shared (.shared .strX10Sp8)), (3636, .shared (.shared .addX9X0_0)),
   (3640, .shared (.shared .addX9X9_16)), (3644, .shared (.shared .movX10_0)),
   (3648, .shared (.shared .strX10X9)), (3652, .shared .storeExpected),
   (3656, .shared (.shared .ldrX10Sp8)), (3660, .shared (.shared .ldrX9Sp)),
   (3664, .shared (.shared .addSp16)), (3668, .bytesTag),
   (3672, .shared (.shared .subSp16)), (3676, .save10), (3680, .save11),
   (3684, .out10), (3688, .add32), (3692, .storeCount), (3696, .zero11),
   (3700, .storeZero11), (3704, .restore11), (3708, .restore10),
   (3712, .shared (.shared .addSp16)), (3716, .actual), (3720, .errorJump)]

macro "byte_tail_follow" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    [Follows, successOps, limitOps, Op.word, Op.effect, UintCodec.Tail.Op.word,
     UintCodec.Tail.Op.effect, UintCodec.Tail.next, UintCodec.Tail.put,
     StoreOp.word, StoreOp.effect, state_simp_rules, BitVec.add_assoc,
     BitVec.sub_eq_add_neg, program, bodyProgram, memcpyProgram, memcpyOffset])

theorem success_block (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4492#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 3 s = block (successOps.map Prod.snd) s := by
  apply follows_run base successOps s hc he ha
  have hpc : r .PC s = base + 4492#64 := hp
  byte_tail_follow <;> simp [hpc, BitVec.add_assoc]

theorem limit_block (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 3576#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 37 s = block (limitOps.map Prod.snd) s := by
  apply follows_run base limitOps s hc he ha
  have hpc : r .PC s = base + 3576#64 := hp
  byte_tail_follow <;> simp [hpc, BitVec.add_assoc]

def successReady (s : ArmState) (base : BitVec 64) : ArmState :=
  afterJump tagStores (block (successOps.map Prod.snd) s) base 4732

def limitReady (s : ArmState) : ArmState :=
  tagsStored (reasonStored (tagInitialized (block (limitOps.map Prod.snd) s)))

theorem success_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4492#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 21 s = returned (successReady s base) := by
  rw [show 21 = 3 + 18 by decide, run_plus, success_block s base hc hp he ha]
  apply tag_tail _ base
  · apply UintCodec.bool_codeAt
    apply uint_codeAt
    simpa only [CodeAt, block_program] using hc
  · have hpc : r .PC s = base + 4492#64 := hp
    simp [successOps, block, Op.effect, UintCodec.Tail.Op.effect,
      UintCodec.Tail.next, UintCodec.Tail.put, state_simp_rules, hpc, BitVec.add_assoc]
  · simpa only [block_error] using he
  · exact block_aligned _ s ha

theorem limit_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 3576#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 48 s = returned (limitReady s) := by
  let t := block (limitOps.map Prod.snd) s
  have htc : BoolCodec.CodeAt t base := UintCodec.bool_codeAt (uint_codeAt (by
    simpa only [t, CodeAt, block_program] using hc))
  have hte : read_err t = .None := by simpa only [t, block_error] using he
  have hta : CheckSPAlignment t := block_aligned _ s ha
  have htp : read_pc t = base + 4720#64 := by
    have hpc : r .PC s = base + 3576#64 := hp
    simp [t, limitOps, block, Op.effect, UintCodec.Tail.Op.effect, UintCodec.Tail.next,
      UintCodec.Tail.put, StoreOp.effect, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 48 = 37 + (3 + 8) by decide, run_plus, limit_block s base hc hp he ha]
  change run (3 + 8) t = _
  rw [run_plus, error_tail t base htc htp hte]
  apply epilogue _ base
  · simpa [BoolCodec.CodeAt, tagsStored, reasonStored, tagInitialized, state_simp_rules] using htc
  · have hpc : r .PC t = base + 4720#64 := htp
    simp [tagsStored, reasonStored, tagInitialized, state_simp_rules, hpc, BitVec.add_assoc]
  · simpa [tagsStored, reasonStored, tagInitialized, state_simp_rules] using hte
  · simpa [tagsStored, reasonStored, tagInitialized, state_simp_rules] using hta

end SszArm.ByteView.Tail
