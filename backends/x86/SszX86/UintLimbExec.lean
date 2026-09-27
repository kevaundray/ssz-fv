import SszX86.UintWidth
import SszWordDecode

namespace SszX86.UintCodec.Large
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

abbrev get (s : MachineData) (r : Reg64) : BitVec 64 := s.regs.get64 r

def put (s : MachineData) (r : Reg64) (v : BitVec 64) : MachineData :=
  {s with regs := s.regs.set64 r v}

def putF (s : MachineData) (r : Reg64) (v : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {put s r v with status := flags}

def subFlags {w : Nat} (a b : BitVec w) : StatusFlags :=
  let v := a - b
  .from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
    of := v.signed != a.signed - b.signed }

@[simp] theorem subFlags_zf {w : Nat} (a b : BitVec w) :
    (subFlags a b).zf = (a == b) := by
  have hz : a - b = 0#w ↔ a = b := by
    constructor
    · intro h
      have := congrArg (fun x : BitVec w => x + b) h
      simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using this
    · rintro rfl
      exact BitVec.sub_self _
  apply Bool.eq_iff_iff.mpr
  simp [subFlags, StatusFlags.from_result, hz]

@[simp] theorem subFlags_cf (a b : BitVec 64) :
    (subFlags a b).cf = decide (a.toNat < b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subFlags, StatusFlags.from_result, bne_iff_ne,
    decide_eq_true_eq, BitVec.unsigned]
  by_cases h : a < b
  · rw [BitVec.toNat_sub_of_lt h]
    have ha := a.isLt
    have hb := b.isLt
    change a.toNat < b.toNat at h
    omega
  · have hle : b ≤ a := Nat.le_of_not_gt h
    rw [BitVec.toNat_sub_of_le hle]
    change ¬ a.toNat < b.toNat at h
    omega

def compare (s : MachineData) (a b : BitVec 64) : MachineData :=
  {s with status := subFlags a b}

def shift (s : MachineData) : Nat := ((get s .rcx).setWidth 8).toNat &&& 63

/-- Every entry is a literal instruction in the linked image, including both NOPs. -/
def offsets : List Nat :=
  [5626, 5630, 5634, 5637, 5641, 5647, 5651, 5657, 5661, 5669,
   5672, 5674, 5677, 5679, 5682, 5692, 5696, 5699, 5705, 5710,
   5713, 5716, 5720, 5723, 5726, 5728]

def instruction (pc : Nat) (s : MachineData) (b : BitVec 8)
    (flags : StatusFlags) : MachineData :=
  match pc with
  | 5626 => putF s .rbx (get s .rbx + BitVec.ofInt 64 (-8)) flags
  | 5630 => putF s .r11 (get s .r11 + 8#64) flags
  | 5634 => compare s (get s .r14) (get s .r10)
  | 5637 => put s .r14 (get s .r14 + 1#64)
  | 5647 => compare s (get s .rbx) 8#64
  | 5651 => put s .r15 8#64
  | 5657 => put s .r15 (if s.status.cf then get s .rbx else get s .r15)
  | 5661 => put s .rax (get s .r14 * 8#64)
  | 5669 => compare s (get s .rbp) (get s .rax)
  | 5674 => put s .rax (get s .r11)
  | 5677 => putF s .rcx 0#64 flags
  | 5679 => putF s .r12 0#64 flags
  | 5696 => compare s (get s .rax) (get s .rsi)
  | 5705 => put s .r13 (b.setWidth 64)
  | 5710 => putF s .r13 (get s .r13 <<< shift s) flags
  | 5713 => putF s .r12 (get s .r12 ||| get s .r13) flags
  | 5716 => putF s .rcx (get s .rcx + 8#64) flags
  | 5720 => putF s .rax (get s .rax + 1#64) flags
  | 5723 => {put s .r15 (get s .r15 - 1#64) with
      status := {subFlags (get s .r15) 1#64 with cf := s.status.cf}}
  | _ => s

def next (pc : Nat) (s : MachineData) : Nat :=
  match pc with
  | 5626 => 5630
  | 5630 => 5634
  | 5634 => 5637
  | 5637 => 5641
  | 5641 => if s.status.zf then 5502 else 5647
  | 5647 => 5651
  | 5651 => 5657
  | 5657 => 5661
  | 5661 => 5669
  | 5669 => 5672
  | 5672 => if s.status.zf then 5619 else 5674
  | 5674 => 5677
  | 5677 => 5679
  | 5679 => 5682
  | 5682 => 5692
  | 5692 => 5696
  | 5696 => 5699
  | 5699 => if s.status.cf then 5705 else 7773
  | 5705 => 5710
  | 5710 => 5713
  | 5713 => 5716
  | 5716 => 5720
  | 5720 => 5723
  | 5723 => 5726
  | 5726 => if s.status.zf then 5728 else 5696
  | 5728 => 5622
  | _ => pc

private theorem cast8 (b : BitVec 8) : BitVec.ofInt 8 (b.toNat : Int) = b := by
  bv_omega

@[simp] private theorem take8 (v : BitVec 64) :
    v.extractLsb' 0 8 = v.setWidth 8 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]

private theorem all_if (P : MachineState → Prop) (p : Prop) [Decidable p]
    (a b : Effects) :
    Effects.All P (if p then a else b) ↔
      (p → Effects.All P a) ∧ (¬p → Effects.All P b) := by
  by_cases h : p <;> simp [h]

@[simp] private theorem mask_lt (n : Nat) : n &&& 63 < 64 := by
  have h : n &&& 63 ≤ 63 := Nat.and_le_right
  omega

@[simp] private theorem mask_one (n : Nat) (h : n &&& 63 = 1) :
    (UInt64.ofNat n &&& 63 : UInt64) = 1 := by
  have hc := congrArg UInt64.ofNat h
  have h63 : UInt64.ofNat 63 = (63 : UInt64) := by decide
  simpa only [UInt64.ofNat_and, h63, UInt64.ofNat_one] using hc

macro "limb_finish " hp:ident "," hl:ident "," s:term ";"
    t1:term "," t2:term "," t3:term "," t4:term : tactic => `(tactic|
  (try simp only [Nat.reduceEqDiff, false_implies, true_implies, get,
      Reg64s.get64] at $hl:ident
   try simp (config := {instances := true})
     [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      MachineData.load, Width.bytes, Width.bits, Effects.All, all_if, ($hl), cast8,
      ($t1), ($t2), ($t3), ($t4), ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
      ConstExpr.interp, BitVec.take, BitVec.signed]
   simp only [instruction, next, put, putF, get, compare, subFlags,
     shift, Reg64s.set64, Reg64s.get64, BitVec.take, BitVec.drop,
     BitVec.signed] at $hp:ident
   repeat' first | apply And.intro | intro
   all_goals try simp_all (config := {instances := true})
     [Effects.All, all_if, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      BitVec.extractLsb'_append_eq_right, BitVec.add_comm, BitVec.add_assoc,
      BitVec.mul_comm, BitVec.take, BitVec.signed, UInt64.add_comm, UInt64.mul_comm]
   all_goals first
     | exact $hp ($s).status
     | exact $hp {($s).status with af := false}
     | exact $hp {($s).status with af := true}
     | exact $hp _))

/-- Keep each ISA normalization in its own kernel declaration. The public
dispatcher below contains no expanded interpreter terms. -/
macro "limb_certificate " name:ident ":" pc:num "," row:num : command => `(command|
  private theorem $name:ident (e : Executable) (base : Int64) (hc : CodeAt e base)
      (s : MachineData) (b : BitVec 8)
      (hl : $pc = 5705 → Mem.loadInt s.dmem (get s .rdx + get s .rax) 1 =
        some (b.toNat : Int)) (P : MachineState → Prop)
      (hp : ∀ flags, Eventually (step e) P
        (instruction $pc s b flags, base + Int64.ofNat (next $pc s))) :
      Eventually (step e) P (s, base + Int64.ofNat $pc) := by
    have t5502 := hc.targets ("u5502", 5502) (by decide)
    have t5619 := hc.targets ("u5619", 5619) (by decide)
    have t5696 := hc.targets ("u5696", 5696) (by decide)
    have t7773 := hc.targets ("boundsPanic", 7773) (by decide)
    uint_width_step $row using hc
    limb_finish hp, hl, s; t5502, t5619, t5696, t7773)

/-- Abstract the immediate before unfolding ADD. The kernel checks its flag
expression once with a symbolic operand, never a huge closed unsigned numeral. -/
private theorem add_rbx_instruction [Labels] (imm : Int64)
    (s : MachineData) (span : Std.Rco Int64)
    (next : MachineData → Effects) (jump : Int64 → MachineData → Effects)
    (post : MachineState → Prop)
    (hp : ∀ flags, Effects.All post
      (next (putF s .rbx (get s .rbx + imm.toBitVec) flags))) :
    Effects.All post (Instr.interp
      (.regular .W64 .W64 (.add (.reg (.low .rbx .W64)) (.imm (.int64 imm))))
      s span next jump) := by
  simp only [putF, put, get, Reg64s.set64, Reg64s.get64] at hp
  simp (config := {instances := true})
    [Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
     ConstExpr.interp, MachineData.set, MachineData.setReg,
     Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
     Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.signed,
     Width.bits, Effects.All]
  simpa (config := {instances := true}) [UInt64.add_comm] using hp _

private theorem row5626 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (b : BitVec 8)
    (_hl : 5626 = 5705 → Mem.loadInt s.dmem (get s .rdx + get s .rax) 1 =
      some (b.toNat : Int)) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (instruction 5626 s b flags, base + Int64.ofNat (next 5626 s))) :
    Eventually (step e) P (s, base + 5626) := by
  letI : Labels := e.labels
  apply step_cps
  have fetched := step_at e base hc (program[190]'(by decide))
    (List.getElem_mem (by decide))
  simp only [program, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
  apply (fetched _ _).mpr
  simp (config := {instances := true})
    [directives, labels, Directives.interp, Directive.interp, Int64.add_assoc]
  apply add_rbx_instruction
  intro flags
  simpa (config := {instances := true})
    [Effects.All, instruction, next, putF, put, get, Reg64s.set64, Reg64s.get64]
    using hp flags

limb_certificate row5630 : 5630, 191
limb_certificate row5634 : 5634, 192
limb_certificate row5637 : 5637, 193
limb_certificate row5641 : 5641, 194
limb_certificate row5647 : 5647, 195
limb_certificate row5651 : 5651, 196
limb_certificate row5657 : 5657, 197
limb_certificate row5661 : 5661, 198
limb_certificate row5669 : 5669, 199
limb_certificate row5672 : 5672, 200
limb_certificate row5674 : 5674, 201
limb_certificate row5677 : 5677, 202
limb_certificate row5679 : 5679, 203
limb_certificate row5682 : 5682, 204
limb_certificate row5692 : 5692, 205
limb_certificate row5696 : 5696, 206
limb_certificate row5699 : 5699, 207
limb_certificate row5705 : 5705, 208
limb_certificate row5710 : 5710, 209
limb_certificate row5713 : 5713, 210
limb_certificate row5716 : 5716, 211
limb_certificate row5720 : 5720, 212
limb_certificate row5723 : 5723, 213
limb_certificate row5726 : 5726, 214
limb_certificate row5728 : 5728, 215

/-- Universal CPS refinement of one actual instruction. Arbitrary flags at the
cut overapproximate, rather than select, all architecturally undefined choices. -/
theorem instruction_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (pc : Nat) (hk : pc ∈ offsets) (s : MachineData) (b : BitVec 8)
    (hl : pc = 5705 → Mem.loadInt s.dmem (get s .rdx + get s .rax) 1 =
      some (b.toNat : Int)) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (instruction pc s b flags, base + Int64.ofNat (next pc s))) :
    Eventually (step e) P (s, base + Int64.ofNat pc) := by
  simp only [offsets, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact row5626 e base hc s b hl P hp
  · exact row5630 e base hc s b hl P hp
  · exact row5634 e base hc s b hl P hp
  · exact row5637 e base hc s b hl P hp
  · exact row5641 e base hc s b hl P hp
  · exact row5647 e base hc s b hl P hp
  · exact row5651 e base hc s b hl P hp
  · exact row5657 e base hc s b hl P hp
  · exact row5661 e base hc s b hl P hp
  · exact row5669 e base hc s b hl P hp
  · exact row5672 e base hc s b hl P hp
  · exact row5674 e base hc s b hl P hp
  · exact row5677 e base hc s b hl P hp
  · exact row5679 e base hc s b hl P hp
  · exact row5682 e base hc s b hl P hp
  · exact row5692 e base hc s b hl P hp
  · exact row5696 e base hc s b hl P hp
  · exact row5699 e base hc s b hl P hp
  · exact row5705 e base hc s b hl P hp
  · exact row5710 e base hc s b hl P hp
  · exact row5713 e base hc s b hl P hp
  · exact row5716 e base hc s b hl P hp
  · exact row5720 e base hc s b hl P hp
  · exact row5723 e base hc s b hl P hp
  · exact row5726 e base hc s b hl P hp
  · exact row5728 e base hc s b hl P hp

/-- The sole store is the real indexed MOV; an ordinary mapped eight-byte load
excludes its fault, without assuming anything about the store's effects. -/
theorem store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old : Int)
    (hm : Mem.loadInt s.dmem (get s .r9 + get s .r14 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P
      ({s with
        dmem := Mem.storeInt s.dmem (get s .r9 + get s .r14 * 8#64)
          8 (get s .r12).toInt}, base + 5626)) :
    Eventually (step e) P (s, base + 5622) := by
  uint_width_step 189 using hc
  simp (config := {instances := true})
    [MachineData.store, Width.bytes, Width.bits,
     BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
     Effects.All, get, Reg64s.get64] at hm ⊢
  rw [hm]
  simpa only [Effects.All, get, Reg64s.get64] using hp

end SszX86.UintCodec.Large
