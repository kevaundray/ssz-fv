import SszArm.CodecLinkedBounded
import SszArm.BoolAlignment
import SszArm.BoolMemory
import SszArm.DelimitedIntegerFacts

namespace SszArm.Codec.Decode.Bounded

inductive Op where
  | p0
  | p4
  | p8
  | p12
  | p16
  | p20
  | p24
  | p28
  | p32
  | p36
  | p40
  | p44
  | p48
  | p52
  | p56
  | p60
  | p64
  | p68
  | p72
  | p76
  | p80
  | p84
  | p88
  | p92
  | p96
  | p100
  | p104
  | p108
  | p112
  | p116
  | p120
  | p124
  | p128
  | p132
  | p136
  | p140
  | p144
  | p148
  | p152
  | p156
  | p160
  | p164
  | p168
  | p172
  | p176
  | p180
  | p184
  | p188
  | p192
  | p196
  | p200
  | p204
  | p208
  | p212
  | p216
  | p220
  | p224
  | p228
  | p232
  | p236
  | p240
  | p244
  | p248
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd100c3ff#32)
  | .p4 => (4, 0xf90003fe#32)
  | .p8 => (8, 0xa90157f6#32)
  | .p12 => (12, 0xa9024ff4#32)
  | .p16 => (16, 0xb9400028#32)
  | .p20 => (20, 0xaa0003f3#32)
  | .p24 => (24, 0x7100051f#32)
  | .p28 => (28, 0x54000541#32)
  | .p32 => (32, 0xa940d835#32)
  | .p36 => (36, 0xaa0203f4#32)
  | .p40 => (40, 0xa9400440#32)
  | .p44 => (44, 0xaa1503e2#32)
  | .p48 => (48, 0xaa1603e3#32)
  | .p52 => (52, 0x97ffb3a7#32)
  | .p56 => (56, 0x13001c08#32)
  | .p60 => (60, 0x7100051f#32)
  | .p64 => (64, 0x5400042b#32)
  | .p68 => (68, 0x52800028#32)
  | .p72 => (72, 0xa9015a75#32)
  | .p76 => (76, 0xd10043ff#32)
  | .p80 => (80, 0xf90003e9#32)
  | .p84 => (84, 0xf90007ea#32)
  | .p88 => (88, 0x91000269#32)
  | .p92 => (92, 0xf9000128#32)
  | .p96 => (96, 0xd280000a#32)
  | .p100 => (100, 0xf900052a#32)
  | .p104 => (104, 0xf94007ea#32)
  | .p108 => (108, 0xf94003e9#32)
  | .p112 => (112, 0x910043ff#32)
  | .p116 => (116, 0xa9402688#32)
  | .p120 => (120, 0xd10043ff#32)
  | .p124 => (124, 0xf90003e9#32)
  | .p128 => (128, 0xf90007ea#32)
  | .p132 => (132, 0x91000269#32)
  | .p136 => (136, 0x9100c129#32)
  | .p140 => (140, 0xd280000a#32)
  | .p144 => (144, 0xf900012a#32)
  | .p148 => (148, 0xd280000a#32)
  | .p152 => (152, 0xf900052a#32)
  | .p156 => (156, 0xf94007ea#32)
  | .p160 => (160, 0xf94003e9#32)
  | .p164 => (164, 0x910043ff#32)
  | .p168 => (168, 0xa9022668#32)
  | .p172 => (172, 0x52800048#32)
  | .p176 => (176, 0xb9004268#32)
  | .p180 => (180, 0xa9424ff4#32)
  | .p184 => (184, 0xa94157f6#32)
  | .p188 => (188, 0xf84307fe#32)
  | .p192 => (192, 0xd65f03c0#32)
  | .p196 => (196, 0xd10043ff#32)
  | .p200 => (200, 0xf90003e9#32)
  | .p204 => (204, 0xf90007ea#32)
  | .p208 => (208, 0x91000269#32)
  | .p212 => (212, 0x91010129#32)
  | .p216 => (216, 0x5280000a#32)
  | .p220 => (220, 0xb900012a#32)
  | .p224 => (224, 0xf94007ea#32)
  | .p228 => (228, 0xf94003e9#32)
  | .p232 => (232, 0x910043ff#32)
  | .p236 => (236, 0xa9424ff4#32)
  | .p240 => (240, 0xa94157f6#32)
  | .p244 => (244, 0xf84307fe#32)
  | .p248 => (248, 0xd65f03c0#32)

abbrev CodeAt := Linked.Bounded.CodeAt

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def save (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 16 (r (.GPR 31#5) s + offset)
    (r (.GPR second) s ++ r (.GPR first) s) s)

def loadPair (first second : BitVec 5) (address : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR second) (read_mem_bytes 8 (address + 8#64) s)
    (put first (read_mem_bytes 8 address s) s)

def compare32 (value : BitVec 64) (number : BitVec 32) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry (value.setWidth 32) (~~~number) 1#1).2 (next s)

def restoreLR (s : ArmState) : ArmState :=
  w (.GPR 31#5) (r (.GPR 31#5) s + 48#64)
    (put 30 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 48#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 30#5) s) s)
  | .p8, s => save 22 21 16#64 s
  | .p12, s => save 20 19 32#64 s
  | .p16, s => put 8 ((read_mem_bytes 4 (r (.GPR 1#5) s) s).setWidth 64) s
  | .p20, s => put 19 (r (.GPR 0#5) s) s
  | .p24, s => compare32 (r (.GPR 8#5) s) 1#32 s
  | .p28, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 32#64 else base + 196#64) s
  | .p32, s => loadPair 21 22 (r (.GPR 1#5) s + 8#64) s
  | .p36, s => put 20 (r (.GPR 2#5) s) s
  | .p40, s => loadPair 0 1 (r (.GPR 2#5) s) s
  | .p44, s => put 2 (r (.GPR 21#5) s) s
  | .p48, s => put 3 (r (.GPR 22#5) s) s
  | .p52, s => w .PC (base - 78128#64) (w (.GPR 30#5) (base + 56#64) s)
  | .p56, s => put 8 ((((r (.GPR 0#5) s).setWidth 8).signExtend 32).setWidth 64) s
  | .p60, s => compare32 (r (.GPR 8#5) s) 1#32 s
  | .p64, s => w .PC (if r (.FLAG .N) s = r (.FLAG .V) s then base + 68#64 else base + 196#64) s
  | .p68, s => put 8 1#64 s
  | .p72, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64) (r (.GPR 22#5) s ++ r (.GPR 21#5) s) s)
  | .p76, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p80, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p84, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p88, s => put 9 (r (.GPR 19#5) s) s
  | .p92, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 8#5) s) s)
  | .p96, s => put 10 0#64 s
  | .p100, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p104, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p108, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p112, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p116, s => loadPair 8 9 (r (.GPR 20#5) s) s
  | .p120, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p124, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p128, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p132, s => put 9 (r (.GPR 19#5) s) s
  | .p136, s => put 9 (r (.GPR 9#5) s + 48#64) s
  | .p140, s => put 10 0#64 s
  | .p144, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p148, s => put 10 0#64 s
  | .p152, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p156, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p160, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p164, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p168, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 32#64) (r (.GPR 9#5) s ++ r (.GPR 8#5) s) s)
  | .p172, s => put 8 2#64 s
  | .p176, s => next (write_mem_bytes 4 (r (.GPR 19#5) s + 64#64) ((r (.GPR 8#5) s).setWidth 32) s)
  | .p180, s => loadPair 20 19 (r (.GPR 31#5) s + 32#64) s
  | .p184, s => loadPair 22 21 (r (.GPR 31#5) s + 16#64) s
  | .p188, s => restoreLR s
  | .p192, s => w .PC (r (.GPR 30#5) s) s
  | .p196, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p200, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p204, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p208, s => put 9 (r (.GPR 19#5) s) s
  | .p212, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p216, s => put 10 0#64 s
  | .p220, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p224, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p228, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p232, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p236, s => loadPair 20 19 (r (.GPR 31#5) s + 32#64) s
  | .p240, s => loadPair 22 21 (r (.GPR 31#5) s + 16#64) s
  | .p244, s => restoreLR s
  | .p248, s => w .PC (r (.GPR 30#5) s) s

/-- Raw instruction execution includes the actual Nat.compare call edge. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have fetched := code op.row (by cases op <;> decide)
  have zero : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, save, loadPair, compare32, restoreLR, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, aligned, pc, BitVec.add_assoc, apply_ite, zero,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.sxt_byte_mask,
       -BitVec.replicate_succ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, save, loadPair, compare32, restoreLR, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, save, loadPair, compare32, restoreLR, state_simp_rules]

theorem aligned_sub48 (address : BitVec 64) (aligned : Aligned address 4) :
    Aligned (address - 48#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

theorem aligned_add48 (address : BitVec 64) (aligned : Aligned address 4) :
    Aligned (address + 48#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

def Op.stackPointer (op : Op) (sp : BitVec 64) : BitVec 64 :=
  match op with
  | .p0 => sp - 48#64
  | .p76 | .p120 | .p196 => sp - 16#64
  | .p112 | .p164 | .p232 => sp + 16#64
  | .p188 | .p244 => sp + 48#64
  | _ => sp

theorem Op.sp (op : Op) (base : BitVec 64) (s : ArmState) :
    r (.GPR 31#5) (op.effect base s) = op.stackPointer (r (.GPR 31#5) s) := by
  cases op <;> simp (config := {decide := true})
    [Op.effect, Op.stackPointer, put, next, save, loadPair, compare32, restoreLR,
     state_simp_rules]

theorem Op.stackPointer_aligned (op : Op) (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (op.stackPointer sp) 4 := by
  cases op <;> simp only [Op.stackPointer]
  case p0 => exact aligned_sub48 sp aligned
  case p76 | p120 | p196 => exact BoolCodec.aligned_sub16 sp aligned
  case p112 | p164 | p232 => exact BoolCodec.aligned_add16 sp aligned
  case p188 | p244 => exact aligned_add48 sp aligned
  all_goals exact aligned

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) :=
  CheckSPAlignment_of_r_sp_aligned (op.sp base s)
    (op.stackPointer_aligned _ (BoolCodec.stack_aligned s aligned))

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op code follows.1 error aligned]
    exact ih _ (by simpa only [CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, Op.program] using code)
      (by simpa only [Op.error] using error) (op.aligned base s aligned) follows.2

end SszArm.Codec.Decode.Bounded
