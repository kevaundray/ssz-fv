import SszArm.NatFromU128Words

namespace SszArm.NatFromU128

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hm : op.row ∈ program := by cases op <;> decide
  have hf : s.program.find? (read_pc s) = some op.row.2 := by
    rw [hp]; exact hc op.row hm
  cases op
  case p0 =>
    simpa only [Op.effect] using word_p0 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p4 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p8 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p12 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p16 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p20 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p24 =>
    simpa only [Op.effect] using word_p24 s base he ha hf
  case p28 =>
    simpa only [Op.effect] using word_p28 s base he ha hf
  case p32 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p36 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p40 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p44 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p48 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p52 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p56 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p60 =>
    simpa only [Op.effect] using word_p60 s base he ha hf
  case p64 =>
    simpa only [Op.effect] using word_p64 s base he ha hf
  case p68 =>
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p72 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p76 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p80 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p84 =>
    simpa only [Op.effect] using word_p84 s base he ha hf
  case p88 =>
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p92 =>
    simpa only [Op.effect] using word_p92 s base he ha hf
  case p96 =>
    simpa only [Op.effect] using word_p96 s base he ha hf
  case p100 =>
    simpa only [Op.effect] using word_p100 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p104 =>
    simpa only [Op.effect] using word_p104 s base he ha hf
  case p108 =>
    simpa only [Op.effect] using word_p108 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p112 =>
    simpa only [Op.effect] using word_p112 s base he ha hf
  case p116 =>
    simpa only [Op.effect] using word_p116 s base he ha hf
  case p120 =>
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p124 =>
    simpa only [Op.effect] using word_p124 s base he ha hf
  case p128 =>
    simpa only [Op.effect] using word_p128 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p132 =>
    simpa only [Op.effect] using word_p132 s base he ha hf
  case p136 =>
    simpa only [Op.effect] using word_p136 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p140 =>
    simpa only [Op.effect] using word_p140 s base he ha hf
  case p144 =>
    simpa only [Op.effect] using word_p144 s base he ha hf
  case p148 =>
    simpa only [Op.effect] using word_p148 s base he ha hf
  case p152 =>
    simpa only [Op.effect] using word_p152 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p156 =>
    simpa only [Op.effect] using word_p156 s base he ha hf
  case p160 =>
    simpa only [Op.effect] using word_p160 s base he ha hf
  case p164 =>
    simpa only [Op.effect] using word_p164 s base he ha hf
  case p168 =>
    simpa only [Op.effect] using word_p168 s base he ha hf
  case p172 =>
    simpa only [Op.effect] using word_p172 s base he ha hf
  case p176 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p180 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p184 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p188 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p192 =>
    simpa only [Op.effect] using word_p60 s base he ha hf
  case p196 =>
    simpa only [Op.effect] using word_p64 s base he ha hf
  case p200 =>
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p204 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p208 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p212 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p216 =>
    simpa only [Op.effect] using word_p84 s base he ha hf
  case p220 =>
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p224 =>
    simpa only [Op.effect] using word_p224 s base he ha hf
  case p228 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p232 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p236 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p240 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p244 =>
    simpa only [Op.effect] using word_p244 s base he ha hf
  case p248 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p252 =>
    simpa only [Op.effect] using word_p24 s base he ha hf
  case p256 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p260 =>
    simpa only [Op.effect] using word_p260 s base he ha hf
  case p264 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p268 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p272 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p276 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p280 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p284 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p288 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p292 =>
    simpa only [Op.effect] using word_p292 s base he ha hf
  case p296 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p300 =>
    simpa only [Op.effect] using word_p24 s base he ha hf
  case p304 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p308 =>
    simpa only [Op.effect] using word_p260 s base he ha hf
  case p312 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p316 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p320 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p324 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p328 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p332 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p336 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p340 =>
    simpa only [Op.effect] using word_p340 s base he ha hf
  case p344 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p348 =>
    simpa only [Op.effect] using word_p24 s base he ha hf
  case p352 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p356 =>
    simpa only [Op.effect] using word_p260 s base he ha hf
  case p360 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p364 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p368 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p372 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p376 =>
    simpa only [Op.effect] using word_p376 s base he ha hf
  case p380 =>
    simpa only [Op.effect] using word_p380 s base he ha hf
  case p384 =>
    simpa only [Op.effect] using word_p384 s base he ha hf
  case p388 =>
    simpa only [Op.effect] using word_p388 s base he ha hf
  case p392 =>
    simpa only [Op.effect] using word_p392 s base he ha hf
  case p396 =>
    simpa only [Op.effect] using word_p396 s base he ha hf
  case p400 =>
    simpa only [Op.effect] using word_p400 s base he ha hf
  case p404 =>
    simpa only [Op.effect] using word_p404 s base he ha hf
  case p408 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p412 =>
    simpa only [Op.effect] using word_p412 s base he ha hf
  case p416 =>
    simpa only [Op.effect] using word_p84 s base he ha hf

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

@[simp] theorem Op.sfp (op : Op) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, Op.program] using hc)
      (by simpa only [Op.error] using he) (op.aligned base s ha) hf.2

@[simp] theorem block_program (base : BitVec 64) (ops : List Op) (s : ArmState) :
    (block base ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program base s)

@[simp] theorem block_error (base : BitVec 64) (ops : List Op) (s : ArmState) :
    read_err (block base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error base s)

theorem block_aligned (base : BitVec 64) (ops : List Op) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (block base ops s) := by
  induction ops generalizing s with
  | nil => exact ha
  | cons op ops ih => exact ih _ (op.aligned base s ha)

end SszArm.NatFromU128
