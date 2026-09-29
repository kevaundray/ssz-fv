import SszArm.IndicesPrefixEqualWidthContract

namespace SszArm.Indices.PrefixEqual.Width

open Udivti3 (next put flagged)

abbrev Side := Clz.Side

def start : Side → Nat | .left => 0 | .right => 220
def pointer : Side → BitVec 5 | .left => 0 | .right => 5
def payload : Side → BitVec 5 | .left => 1 | .right => 6
def lower : Side → BitVec 5 | .left => 8 | .right => 12
def upper : Side → BitVec 5 | .left => 10 | .right => 14
def limb : Side → BitVec 5 | .left => 9 | .right => 13
def count : Side → BitVec 5 | .left => 11 | .right => 15
def high : Side → BitVec 5 | .left => 12 | .right => 16

/-- Relative offsets of the real width prologue, excluding the already-proved
three-instruction CLZ loop and the separate width-subtraction blocks. -/
inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44
  | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88
  | p92 | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128
  | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176
  | p180 | p184 | p188 | p192
  deriving DecidableEq

def Op.offset : Op → Nat
  | .p0 => 0 | .p4 => 4 | .p8 => 8 | .p12 => 12 | .p16 => 16 | .p20 => 20
  | .p24 => 24 | .p28 => 28 | .p32 => 32 | .p36 => 36 | .p40 => 40 | .p44 => 44
  | .p48 => 48 | .p52 => 52 | .p56 => 56 | .p60 => 60 | .p64 => 64 | .p68 => 68
  | .p72 => 72 | .p76 => 76 | .p80 => 80 | .p84 => 84 | .p88 => 88 | .p92 => 92
  | .p96 => 96 | .p100 => 100 | .p104 => 104 | .p108 => 108 | .p112 => 112
  | .p116 => 116 | .p120 => 120 | .p124 => 124 | .p128 => 128 | .p144 => 144
  | .p148 => 148 | .p152 => 152 | .p156 => 156 | .p160 => 160 | .p164 => 164
  | .p168 => 168 | .p172 => 172 | .p176 => 176 | .p180 => 180 | .p184 => 184
  | .p188 => 188 | .p192 => 192

def Op.word : Side → Op → BitVec 32
  | .left, .p0 => 0xb40002a0 | .right, .p0 => 0xb40002a5
  | .left, .p4 => 0xd1002008 | .right, .p4 => 0xd10020ac
  | .left, .p8 => 0xaa0103eb | .right, .p8 => 0xaa0603ef
  | .left, .p12 => 0xb40005ab | .right, .p12 => 0xb40005af
  | _, .p16 => 0xd10043ff
  | .left, .p20 => 0xf90003ea | .right, .p20 => 0xf90003e9
  | .left, .p24 => 0xaa0b03ea | .right, .p24 => 0xaa0f03e9
  | .left, .p28 => 0xd37df14a | .right, .p28 => 0xd37df129
  | .left, .p32 => 0x8b0a010a | .right, .p32 => 0x8b090189
  | .left, .p36 => 0xf9400149 | .right, .p36 => 0xf940012d
  | .left, .p40 => 0xf94003ea | .right, .p40 => 0xf94003e9
  | _, .p44 => 0x910043ff
  | .left, .p48 => 0xaa0b03ea | .right, .p48 => 0xaa0f03ee
  | .left, .p52 => 0xd100056b | .right, .p52 => 0xd10005ef
  | .left, .p56 => 0xb4fffea9 | .right, .p56 => 0xb4fffead
  | .left, .p60 => 0xd37ae548 | .right, .p60 => 0xd37ae5cc
  | .left, .p64 => 0xd37afd4a | .right, .p64 => 0xd37afdce
  | .left, .p68 => 0x9280000b | .right, .p68 => 0x9280000f
  | .left, .p72 => 0xf1010108 | .right, .p72 => 0xf101018c
  | .left, .p76 => 0x9a0b014a | .right, .p76 => 0x9a0f01ce
  | _, .p80 => 0x14000007
  | .left, .p84 => 0xaa1f03e8 | .right, .p84 => 0xaa1f03ec
  | .left, .p88 => 0xaa1f03ea | .right, .p88 => 0xaa1f03ee
  | .left, .p92 => 0xaa1f03eb | .right, .p92 => 0xaa1f03ef
  | .left, .p96 => 0xaa1f03ec | .right, .p96 => 0xaa1f03f0
  | .left, .p100 => 0xaa0103e9 | .right, .p100 => 0xaa0603ed
  | .left, .p104 => 0xb40002e1 | .right, .p104 => 0xb40002e6
  | _, .p108 => 0xd10043ff
  | .left, .p112 => 0xf90003ea | .right, .p112 => 0xf90003e9
  | .left, .p116 => 0xf90007eb | .right, .p116 => 0xf90007ea
  | .left, .p120 => 0xaa0903ea | .right, .p120 => 0xaa0d03e9
  | .left, .p124 => 0xd280080b | .right, .p124 => 0xd280080a
  | .left, .p128 => 0xb400008a | .right, .p128 => 0xb4000089
  | .left, .p144 => 0xaa0b03e9 | .right, .p144 => 0xaa0a03ed
  | .left, .p148 => 0xf94007eb | .right, .p148 => 0xf94007ea
  | .left, .p152 => 0xf94003ea | .right, .p152 => 0xf94003e9
  | _, .p156 => 0x910043ff
  | .left, .p160 => 0x5280080b | .right, .p160 => 0x5280080f
  | .left, .p164 => 0x4b090169 | .right, .p164 => 0x4b0d01ed
  | .left, .p168 => 0xab09010b | .right, .p168 => 0xab0d018f
  | _, .p172 => 0x54000062
  | .left, .p176 => 0xaa0a03ec | .right, .p176 => 0xaa0e03f0
  | _, .p180 => 0x14000002
  | .left, .p184 => 0x9100054c | .right, .p184 => 0x910005d0
  | _, .p188 => 0x14000002
  | .left, .p192 => 0xaa1f03ec | .right, .p192 => 0xaa1f03f0

def Op.row (side : Side) (op : Op) : Nat × BitVec 32 :=
  (start side + op.offset, op.word side)

def atPC (side : Side) (base : BitVec 64) (offset : Nat) : BitVec 64 :=
  base + BitVec.ofNat 64 (start side + offset)

def Op.effect (side : Side) (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (atPC side base (if r (.GPR (pointer side)) s = 0#64 then 84 else 4)) s
  | .p4, s => put (lower side) (r (.GPR (pointer side)) s - 8#64) s
  | .p8, s => put (count side) (r (.GPR (payload side)) s) s
  | .p12, s => w .PC (atPC side base (if r (.GPR (count side)) s = 0#64 then 192 else 16)) s
  | .p16, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p20, s => write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR side.input) s) (next s)
  | .p24, s => put side.input (r (.GPR (count side)) s) s
  | .p28, s => put side.input (r (.GPR side.input) s <<< 3) s
  | .p32, s => put side.input (r (.GPR (lower side)) s + r (.GPR side.input) s) s
  | .p36, s => put (limb side) (read_mem_bytes 8 (r (.GPR side.input) s) s) s
  | .p40, s => put side.input (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p44, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p48, s => put (upper side) (r (.GPR (count side)) s) s
  | .p52, s => put (count side) (r (.GPR (count side)) s - 1#64) s
  | .p56, s => w .PC (atPC side base (if r (.GPR (limb side)) s = 0#64 then 12 else 60)) s
  | .p60, s => put (lower side) (r (.GPR (upper side)) s <<< 6) s
  | .p64, s => put (upper side) (r (.GPR (upper side)) s >>> 58) s
  | .p68, s => put (count side) (-1#64) s
  | .p72, s => flagged (lower side) (r (.GPR (lower side)) s) (~~~64#64) 1#1 s
  | .p76, s => put (upper side) (AddWithCarry (r (.GPR (upper side)) s)
      (r (.GPR (count side)) s) (r (.FLAG .C) s)).1 s
  | .p80, s => w .PC (atPC side base 108) s
  | .p84, s => put (lower side) 0#64 s
  | .p88, s => put (upper side) 0#64 s
  | .p92, s => put (count side) 0#64 s
  | .p96, s => put (high side) 0#64 s
  | .p100, s => put (limb side) (r (.GPR (payload side)) s) s
  | .p104, s => w .PC (atPC side base (if r (.GPR (payload side)) s = 0#64 then 196 else 108)) s
  | .p108, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p112, s => write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR side.input) s) (next s)
  | .p116, s => write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR side.counter) s) (next s)
  | .p120, s => put side.input (r (.GPR (limb side)) s) s
  | .p124, s => put side.counter 64#64 s
  | .p128, s => w .PC (atPC side base (if r (.GPR side.input) s = 0#64 then 144 else 132)) s
  | .p144, s => put (limb side) (r (.GPR side.counter) s) s
  | .p148, s => put side.counter (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p152, s => put side.input (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p156, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p160, s => put (count side) 64#64 s
  | .p164, s => put (limb side)
      (((r (.GPR (count side)) s).setWidth 32 - (r (.GPR (limb side)) s).setWidth 32).setWidth 64) s
  | .p168, s => flagged (count side) (r (.GPR (lower side)) s) (r (.GPR (limb side)) s) 0#1 s
  | .p172, s => w .PC (atPC side base (if r (.FLAG .C) s = 1#1 then 184 else 176)) s
  | .p176, s => put (high side) (r (.GPR (upper side)) s) s
  | .p180, s => w .PC (atPC side base 188) s
  | .p184, s => put (high side) (r (.GPR (upper side)) s + 1#64) s
  | .p188, s => w .PC (atPC side base 196) s
  | .p192, s => put (high side) 0#64 s

theorem step (side : Side) (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = atPC side base op.offset) :
    stepi s = op.effect side base s := by
  have fetched := code (op.row side) (by cases side <;> cases op <;> decide)
  cases side <;> cases op
  all_goals
    simp only [Op.row, Op.offset, Op.word, atPC, start, Nat.reduceAdd] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, atPC, start, pointer, payload, lower, upper, limb, count, high,
        Clz.Side.input, Clz.Side.counter, next, put, flagged, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, aligned,
        pc, BitVec.add_assoc, BitVec.sub_eq_add_neg, apply_ite]
  all_goals first | rfl | (split <;> simp_all)

@[simp] theorem Op.program (side : Side) (base : BitVec 64) (op : Op) (s : ArmState) :
    (op.effect side base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, flagged, state_simp_rules]

@[simp] theorem Op.error (side : Side) (base : BitVec 64) (op : Op) (s : ArmState) :
    read_err (op.effect side base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, flagged, state_simp_rules]

theorem Op.aligned (side : Side) (base : BitVec 64) (op : Op) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect side base s) := by
  cases side <;> cases op <;>
    simp [Op.effect, lower, upper, limb, count, high, Clz.Side.input, Clz.Side.counter,
      put, next, flagged, state_simp_rules, aligned]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

def block (side : Side) (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect side base t) s

def Follows (side : Side) (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = atPC side base op.offset ∧
      Follows side base rest (op.effect side base s)

theorem block_run (side : Side) (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows side base ops s) :
    run ops.length s = block side base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      change run (rest.length + 1) s = block side base rest (op.effect side base s)
      rw [run, step side op s base code error aligned follows.1]
      exact ih _ (Codec.Linked.WordsAt.preserve code (op.program side base s))
        ((op.error side base s).trans error) (op.aligned side base s aligned) follows.2

end SszArm.Indices.PrefixEqual.Width
