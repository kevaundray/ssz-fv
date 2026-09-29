import SszArm.HashContract

namespace SszArm.Hash.Combine

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44
  | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92
  | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136
  | p140 | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176
  | p180 | p184 | p188 | p192 | p196 | p200 | p204 | p208 | p212 | p216
  | p220 | p224 | p228 | p232 | p236 | p240 | p244 | p248 | p252 | p256
  | p260 | p264 | p268 | p272 | p276 | p280 | p284 | p288 | p292 | p296
  | p300 | p304 | p308 | p312 | p316 | p320 | p324 | p328 | p332 | p336
  | p340 | p344 | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376
  | p380 | p384 | p388 | p392 | p396 | p400 | p404 | p408 | p412 | p416
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd104c3ff#32)
  | .p4 => (4, 0xf90073fd#32)
  | .p8 => (8, 0xa90f67fe#32)
  | .p12 => (12, 0xa9105ff8#32)
  | .p16 => (16, 0xa91157f6#32)
  | .p20 => (20, 0xa9124ff4#32)
  | .p24 => (24, 0x6f00e400#32)
  | .p28 => (28, 0x910003f8#32)
  | .p32 => (32, 0xaa0203f6#32)
  | .p36 => (36, 0xaa0103f7#32)
  | .p40 => (40, 0xaa0003f3#32)
  | .p44 => (44, 0xd503201f#32)
  | .p48 => (48, 0x10ea2ea1#32)
  | .p52 => (52, 0x91010300#32)
  | .p56 => (56, 0x52800402#32)
  | .p60 => (60, 0xaa0403f4#32)
  | .p64 => (64, 0xaa0303f5#32)
  | .p68 => (68, 0xad0003e0#32)
  | .p72 => (72, 0xad0103e0#32)
  | .p76 => (76, 0x94008598#32)
  | .p80 => (80, 0xf10102df#32)
  | .p84 => (84, 0xd10043ff#32)
  | .p88 => (88, 0xf90003e9#32)
  | .p92 => (92, 0xf90007ea#32)
  | .p96 => (96, 0x910043e9#32)
  | .p100 => (100, 0x91018129#32)
  | .p104 => (104, 0xd280000a#32)
  | .p108 => (108, 0xf900012a#32)
  | .p112 => (112, 0xf9000536#32)
  | .p116 => (116, 0xf94007ea#32)
  | .p120 => (120, 0xf94003e9#32)
  | .p124 => (124, 0x910043ff#32)
  | .p128 => (128, 0x54000103#32)
  | .p132 => (132, 0x91010300#32)
  | .p136 => (136, 0xaa1703e1#32)
  | .p140 => (140, 0x97fffe1b#32)
  | .p144 => (144, 0xd10102d6#32)
  | .p148 => (148, 0x910102f7#32)
  | .p152 => (152, 0xf100fedf#32)
  | .p156 => (156, 0x54ffff48#32)
  | .p160 => (160, 0x910003e0#32)
  | .p164 => (164, 0xaa1703e1#32)
  | .p168 => (168, 0xaa1603e2#32)
  | .p172 => (172, 0x910003f9#32)
  | .p176 => (176, 0x9400857f#32)
  | .p180 => (180, 0xf94037e8#32)
  | .p184 => (184, 0x8b140108#32)
  | .p188 => (188, 0xa90623f6#32)
  | .p192 => (192, 0xb40003b6#32)
  | .p196 => (196, 0x52800808#32)
  | .p200 => (200, 0x8b160320#32)
  | .p204 => (204, 0xaa1503e1#32)
  | .p208 => (208, 0xcb160108#32)
  | .p212 => (212, 0xeb08029f#32)
  | .p216 => (216, 0x9a883297#32)
  | .p220 => (220, 0xaa1703e2#32)
  | .p224 => (224, 0x94008573#32)
  | .p228 => (228, 0xf94033e8#32)
  | .p232 => (232, 0x8b170108#32)
  | .p236 => (236, 0xf101011f#32)
  | .p240 => (240, 0xf90033e8#32)
  | .p244 => (244, 0x540003c3#32)
  | .p248 => (248, 0x91010300#32)
  | .p252 => (252, 0x910003e1#32)
  | .p256 => (256, 0x8b1702b5#32)
  | .p260 => (260, 0xcb170294#32)
  | .p264 => (264, 0x97fffdfc#32)
  | .p268 => (268, 0xd10043ff#32)
  | .p272 => (272, 0xf90003e9#32)
  | .p276 => (276, 0xf90007ea#32)
  | .p280 => (280, 0x910043e9#32)
  | .p284 => (284, 0x91018129#32)
  | .p288 => (288, 0xd280000a#32)
  | .p292 => (292, 0xf900012a#32)
  | .p296 => (296, 0xf94007ea#32)
  | .p300 => (300, 0xf94003e9#32)
  | .p304 => (304, 0x910043ff#32)
  | .p308 => (308, 0xf101029f#32)
  | .p312 => (312, 0x54000103#32)
  | .p316 => (316, 0x91010300#32)
  | .p320 => (320, 0xaa1503e1#32)
  | .p324 => (324, 0x97fffded#32)
  | .p328 => (328, 0xd1010294#32)
  | .p332 => (332, 0x910102b5#32)
  | .p336 => (336, 0xf100fe9f#32)
  | .p340 => (340, 0x54ffff48#32)
  | .p344 => (344, 0x910003e0#32)
  | .p348 => (348, 0xaa1503e1#32)
  | .p352 => (352, 0xaa1403e2#32)
  | .p356 => (356, 0x94008552#32)
  | .p360 => (360, 0xf90033f4#32)
  | .p364 => (364, 0x9101c3e0#32)
  | .p368 => (368, 0x910003e1#32)
  | .p372 => (372, 0x52800e02#32)
  | .p376 => (376, 0x9400854d#32)
  | .p380 => (380, 0x9101c3e1#32)
  | .p384 => (384, 0xaa1303e0#32)
  | .p388 => (388, 0x97ffff0e#32)
  | .p392 => (392, 0xa9524ff4#32)
  | .p396 => (396, 0xf94073fd#32)
  | .p400 => (400, 0xa95157f6#32)
  | .p404 => (404, 0xa9505ff8#32)
  | .p408 => (408, 0xa94f67fe#32)
  | .p412 => (412, 0x9104c3ff#32)
  | .p416 => (416, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  next (w (.GPR reg) value s)

def store (reg address : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 8 (r (.GPR address) s + offset) (r (.GPR reg) s) s)

def load (reg address : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  put reg (read_mem_bytes 8 (r (.GPR address) s + offset) s) s

def save (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 16 (r (.GPR 31#5) s + offset)
    (r (.GPR second) s ++ r (.GPR first) s) s)

def restore (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  let value := read_mem_bytes 16 (r (.GPR 31#5) s + offset) s
  next (w (.GPR second) (value.extractLsb' 64 64)
    (w (.GPR first) (value.extractLsb' 0 64) s))

def compare (left right : BitVec 64) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry left (~~~right) 1#1).2 (next s)

def branch (condition : BitVec 4) (offset : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (if ConditionHolds condition s then read_pc s + offset else read_pc s + 4#64) s

def call (offset : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (read_pc s + offset) (w (.GPR 30#5) (read_pc s + 4#64) s)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 304#64) s
  | .p4, s => store 29 31 224 s
  | .p8, s => save 30 25 240 s
  | .p12, s => save 24 23 256 s
  | .p16, s => save 22 21 272 s
  | .p20, s => save 20 19 288 s
  | .p24, s => next (w (.SFP 0#5) 0#128 s)
  | .p28, s => put 24 (r (.GPR 31#5) s) s
  | .p32, s => put 22 (r (.GPR 2#5) s) s
  | .p36, s => put 23 (r (.GPR 1#5) s) s
  | .p40, s => put 19 (r (.GPR 0#5) s) s
  | .p44, s => next s
  | .p48, s => put 1 (read_pc s + BitVec.ofInt 64 (-178732)) s
  | .p52, s | .p132, s | .p248, s | .p316, s => put 0 (r (.GPR 24#5) s + 64#64) s
  | .p56, s => put 2 32 s
  | .p60, s => put 20 (r (.GPR 4#5) s) s
  | .p64, s => put 21 (r (.GPR 3#5) s) s
  | .p68, s => next (write_mem_bytes 32 (r (.GPR 31#5) s)
      (r (.SFP 0#5) s ++ r (.SFP 0#5) s) s)
  | .p72, s => next (write_mem_bytes 32 (r (.GPR 31#5) s + 32#64)
      (r (.SFP 0#5) s ++ r (.SFP 0#5) s) s)
  | .p76, s => call 136800 s
  | .p80, s => compare (r (.GPR 22#5) s) 64 s
  | .p84, s | .p268, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p88, s | .p272, s => store 9 31 0 s
  | .p92, s | .p276, s => store 10 31 8 s
  | .p96, s | .p280, s => put 9 (r (.GPR 31#5) s + 16#64) s
  | .p100, s | .p284, s => put 9 (r (.GPR 9#5) s + 96#64) s
  | .p104, s | .p288, s => put 10 0 s
  | .p108, s | .p292, s => store 10 9 0 s
  | .p112, s => store 22 9 8 s
  | .p116, s | .p296, s => load 10 31 8 s
  | .p120, s | .p300, s => load 9 31 0 s
  | .p124, s | .p304, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p128, s | .p312, s => branch 3 32 s
  | .p136, s | .p164, s => put 1 (r (.GPR 23#5) s) s
  | .p140, s => call (BitVec.ofInt 64 (-1940)) s
  | .p144, s => put 22 (r (.GPR 22#5) s - 64#64) s
  | .p148, s => put 23 (r (.GPR 23#5) s + 64#64) s
  | .p152, s => compare (r (.GPR 22#5) s) 63 s
  | .p156, s | .p340, s => branch 8 (BitVec.ofInt 64 (-24)) s
  | .p160, s | .p344, s => put 0 (r (.GPR 31#5) s) s
  | .p168, s => put 2 (r (.GPR 22#5) s) s
  | .p172, s => put 25 (r (.GPR 31#5) s) s
  | .p176, s => call 136700 s
  | .p180, s => load 8 31 104 s
  | .p184, s => put 8 (r (.GPR 8#5) s + r (.GPR 20#5) s) s
  | .p188, s => save 22 8 96 s
  | .p192, s => w .PC
      (if r (.GPR 22#5) s = 0#64 then read_pc s + 116#64 else read_pc s + 4#64) s
  | .p196, s => put 8 64 s
  | .p200, s => put 0 (r (.GPR 25#5) s + r (.GPR 22#5) s) s
  | .p204, s | .p320, s | .p348, s => put 1 (r (.GPR 21#5) s) s
  | .p208, s => put 8 (r (.GPR 8#5) s - r (.GPR 22#5) s) s
  | .p212, s => compare (r (.GPR 20#5) s) (r (.GPR 8#5) s) s
  | .p216, s => put 23 (if ConditionHolds 3 s then r (.GPR 20#5) s else r (.GPR 8#5) s) s
  | .p220, s => put 2 (r (.GPR 23#5) s) s
  | .p224, s => call 136652 s
  | .p228, s => load 8 31 96 s
  | .p232, s => put 8 (r (.GPR 8#5) s + r (.GPR 23#5) s) s
  | .p236, s => compare (r (.GPR 8#5) s) 64 s
  | .p240, s => store 8 31 96 s
  | .p244, s => branch 3 120 s
  | .p252, s | .p368, s => put 1 (r (.GPR 31#5) s) s
  | .p256, s => put 21 (r (.GPR 21#5) s + r (.GPR 23#5) s) s
  | .p260, s => put 20 (r (.GPR 20#5) s - r (.GPR 23#5) s) s
  | .p264, s => call (BitVec.ofInt 64 (-2064)) s
  | .p308, s => compare (r (.GPR 20#5) s) 64 s
  | .p324, s => call (BitVec.ofInt 64 (-2124)) s
  | .p328, s => put 20 (r (.GPR 20#5) s - 64#64) s
  | .p332, s => put 21 (r (.GPR 21#5) s + 64#64) s
  | .p336, s => compare (r (.GPR 20#5) s) 63 s
  | .p352, s => put 2 (r (.GPR 20#5) s) s
  | .p356, s => call 136520 s
  | .p360, s => store 20 31 96 s
  | .p364, s => put 0 (r (.GPR 31#5) s + 112#64) s
  | .p372, s => put 2 112 s
  | .p376, s => call 136500 s
  | .p380, s => put 1 (r (.GPR 31#5) s + 112#64) s
  | .p384, s => put 0 (r (.GPR 19#5) s) s
  | .p388, s => call (BitVec.ofInt 64 (-968)) s
  | .p392, s => restore 20 19 288 s
  | .p396, s => load 29 31 224 s
  | .p400, s => restore 22 21 272 s
  | .p404, s => restore 24 23 256 s
  | .p408, s => restore 30 25 240 s
  | .p412, s => put 31 (r (.GPR 31#5) s + 304#64) s
  | .p416, s => w .PC (r (.GPR 30#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := code.combine op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, store, load, save, restore, compare, branch, call,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
       BitVec.sub_eq_add_neg, BitVec.setWidth_eq]
  all_goals arm_state_nf
  case p24 =>
    exact w_of_w_commute (fld1 := .SFP 0#5) (fld2 := .PC) (by decide)
  all_goals try simp only [show BitVec.partInstall 0 16 0#16 0#64 = 0#64 by decide]
  all_goals split <;> rename_i condition <;> simp only [condition, ↓reduceIte]

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, store, load, save, restore,
    compare, branch, call, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, store, load, save, restore,
    compare, branch, call, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact induction _ (code.of_program_eq (op.program s))
      ((op.error s).trans error) follows.2.2

@[simp] theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih (op.effect s)).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih (op.effect s)).trans (op.error s)

end SszArm.Hash.Combine
