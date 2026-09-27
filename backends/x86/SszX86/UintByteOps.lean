import SszX86.UintWidth
import SszWordDecode

namespace SszX86.UintCodec.Small
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

def compare {w : Nat} (s : MachineData) (a b : BitVec w) : MachineData :=
  {s with status := subFlags a b}

abbrev low32 (v : BitVec 64) : BitVec 64 := (v.setWidth 32).setWidth 64
abbrev low8 (v : BitVec 64) : BitVec 8 := v.setWidth 8

@[simp] private theorem take32 (v : BitVec 64) :
    v.extractLsb' 0 32 = v.setWidth 32 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]

@[simp] private theorem take8 (v : BitVec 64) :
    v.extractLsb' 0 8 = v.setWidth 8 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]

def replace8 (v : BitVec 64) (b : BitVec 8) : BitVec 64 :=
  v.replaceLow b

/-- The actual x86 CL mask; in particular, byte writes do not zero the rest of RCX. -/
def shift (s : MachineData) : Nat := (low8 (get s .rcx)).toNat &&& 63

/-- Offsets covered by the byte-trim/Small instruction certificate. No stores,
stack operations, arena loads, or surrogate instructions occur in this list. -/
def offsets : List Nat :=
  [2800, 2804, 2810, 2815, 2818, 2820, 2824, 2828, 2830, 2834,
   2840, 2843, 2846, 5354, 5357, 5361, 5364, 5367, 5370, 5375,
   5378, 5380, 5382, 5385, 5391, 5394, 5397, 5400, 5406, 5409,
   5412, 5415, 5418, 5424, 5426, 5428, 5431, 5435, 5438, 5442,
   5445, 5447, 5450, 5454, 5456, 5460, 5463, 5466, 5468, 5473,
   5476, 5479, 5482, 5485, 5488, 5492, 5495, 5497, 5499]

def loads (pc : Nat) : Bool :=
  pc == 2810 || pc == 5370 || pc == 5385 || pc == 5400 || pc == 5418 || pc == 5468

def address (pc : Nat) (s : MachineData) : BitVec 64 :=
  match pc with
  | 2810 => get s .rdx + get s .rax - 1#64
  | 5370 => get s .rdx + get s .r10
  | 5385 => get s .rdx + get s .r10 + 1#64
  | 5400 => get s .rdx + get s .r10 + 2#64
  | 5418 => get s .rdx + get s .r10 + 3#64
  | 5468 => get s .rdx + get s .rax
  | _ => 0#64

/-- Register effects of the literal instructions. Only dead arithmetic flags
are abstracted. CMP, TEST and the trim SUB retain precisely the flags read by
subsequent conditional branches; MOV retains them as well. -/
def instruction (pc : Nat) (s : MachineData) (b : BitVec 8)
    (flags : StatusFlags) : MachineData :=
  match pc with
  | 2800 => put (compare s (get s .r10) 1#64) .r10 (get s .r10 - 1#64)
  | 2810 => compare s b 0#8
  | 2815 => put s .rax (get s .r10)
  | 2820 => put s .rbp (get s .r10 + 1#64)
  | 2824 => compare s (get s .rbp) 9#64
  | 2830 => compare s (get s .rbp) 4#64
  | 2840 | 5364 => putF s .r8 0#64 flags
  | 2843 | 5367 => putF s .r10 0#64 flags
  | 5354 => put s .r9 (low32 (get s .rbp))
  | 5357 => putF s .r9 (((get s .r9).setWidth 32 &&& 12#32).setWidth 64) flags
  | 5361 => putF s .r11 0#64 flags
  | 5370 => put s .rbx (b.setWidth 64)
  | 5375 => put s .rax (low32 (get s .r11))
  | 5378 => putF s .rax (replace8 (get s .rax) (low8 (get s .rax) &&& 32#8)) flags
  | 5380 | 5426 => put s .rcx (low32 (get s .rax))
  | 5382 => putF s .rbx (get s .rbx <<< shift s) flags
  | 5385 => put s .r14 (b.setWidth 64)
  | 5391 => put s .rcx (low32 (get s .rax + 8#64))
  | 5394 => putF s .r14 (get s .r14 <<< shift s) flags
  | 5397 => putF s .rbx (get s .rbx ||| get s .r8) flags
  | 5400 => put s .r15 (b.setWidth 64)
  | 5406 => put s .rcx (low32 (get s .rax + 16#64))
  | 5409 => putF s .r15 (get s .r15 <<< shift s) flags
  | 5412 => putF s .r15 (get s .r15 ||| get s .r14) flags
  | 5415 => putF s .r15 (get s .r15 ||| get s .rbx) flags
  | 5418 => put s .r8 (b.setWidth 64)
  | 5424 => putF s .rax (replace8 (get s .rax) (low8 (get s .rax) ||| 24#8)) flags
  | 5428 => putF s .r8 (get s .r8 <<< shift s) flags
  | 5431 => putF s .r10 (get s .r10 + 4#64) flags
  | 5435 => putF s .r8 (get s .r8 ||| get s .r15) flags
  | 5438 => putF s .r11 (get s .r11 + 32#64) flags
  | 5442 => compare s (get s .r9) (get s .r10)
  | 5447 => putF s .rdx (get s .rdx + get s .r10) flags
  | 5450 => {s with status := (StatusFlags.from_result
      (low8 (get s .rbp) &&& 3#8) {cf := false, af := flags.af, of := false})}
  | 5456 => putF s .r10 (get s .r10 <<< 3) flags
  | 5460 => putF s .rbp (((get s .rbp).setWidth 32 &&& 3#32).setWidth 64) flags
  | 5463 | 5499 => putF s .r9 0#64 flags
  | 5466 => putF s .rax 0#64 flags
  | 5468 => put s .r11 (b.setWidth 64)
  | 5473 => put s .rcx (low32 (get s .r10))
  | 5476 => putF s .rcx (replace8 (get s .rcx) (low8 (get s .rcx) &&& 56#8)) flags
  | 5479 => putF s .r11 (get s .r11 <<< shift s) flags
  | 5482 => putF s .r8 (get s .r8 ||| get s .r11) flags
  | 5485 => putF s .rax (get s .rax + 1#64) flags
  | 5488 => putF s .r10 (get s .r10 + 8#64) flags
  | 5492 => compare s (get s .rbp) (get s .rax)
  | _ => s

def next (pc : Nat) (s : MachineData) : Nat :=
  match pc with
  | 2800 => 2804
  | 2804 => if s.status.cf then 5499 else 2810
  | 2810 => 2815
  | 2815 => 2818
  | 2818 => if s.status.zf then 2800 else 2820
  | 2820 => 2824
  | 2824 => 2828
  | 2828 => if s.status.cf then 2830 else 2896
  | 2830 => 2834
  | 2834 => if s.status.cf then 2840 else 5354
  | 2840 => 2843
  | 2843 => 2846
  | 2846 => 5450
  | 5354 => 5357
  | 5357 => 5361
  | 5361 => 5364
  | 5364 => 5367
  | 5367 => 5370
  | 5370 => 5375
  | 5375 => 5378
  | 5378 => 5380
  | 5380 => 5382
  | 5382 => 5385
  | 5385 => 5391
  | 5391 => 5394
  | 5394 => 5397
  | 5397 => 5400
  | 5400 => 5406
  | 5406 => 5409
  | 5409 => 5412
  | 5412 => 5415
  | 5415 => 5418
  | 5418 => 5424
  | 5424 => 5426
  | 5426 => 5428
  | 5428 => 5431
  | 5431 => 5435
  | 5435 => 5438
  | 5438 => 5442
  | 5442 => 5445
  | 5445 => if s.status.zf then 5447 else 5370
  | 5447 => 5450
  | 5450 => 5454
  | 5454 => if s.status.zf then 5499 else 5456
  | 5456 => 5460
  | 5460 => 5463
  | 5463 => 5466
  | 5466 => 5468
  | 5468 => 5473
  | 5473 => 5476
  | 5476 => 5479
  | 5479 => 5482
  | 5482 => 5485
  | 5485 => 5488
  | 5488 => 5492
  | 5492 => 5495
  | 5495 => if s.status.zf then 5497 else 5468
  | 5497 | 5499 => 5502
  | _ => pc

private theorem cast8 (b : BitVec 8) : BitVec.ofInt 8 (b.toNat : Int) = b := by
  bv_omega

/-- Split only control choices of the effect tree, never expressions inside an
already reached machine state (such as the signed overflow calculation). -/
private theorem all_if (P : MachineState → Prop) (p : Prop) [Decidable p]
    (a b : Effects) :
    Effects.All P (if p then a else b) ↔
      (p → Effects.All P a) ∧ (¬p → Effects.All P b) := by
  by_cases h : p <;> simp [h]

@[simp] private theorem mask_lt (n : Nat) : n &&& 63 < 64 := by
  have h : n &&& 63 ≤ 63 := Nat.and_le_right
  omega

/-- The count-one OF branch is decided in Nat, but register simplification
distributes the count cast over AND. Retain that branch fact across the cast. -/
@[simp] private theorem mask_one (n : Nat) (h : n &&& 63 = 1) :
    (UInt64.ofNat n &&& 63 : UInt64) = 1 := by
  have hc := congrArg UInt64.ofNat h
  have h63 : UInt64.ofNat 63 = (63 : UInt64) := by decide
  simpa only [UInt64.ofNat_and, h63, UInt64.ofNat_one] using hc

macro "uint_byte_finish " s:term " load " hl:ident " cont " hp:ident : tactic => `(tactic|
  (simp [loads, address, get, Reg64s.get64, BitVec.sub_eq_add_neg,
      BitVec.add_assoc] at $hl:ident
   try simp (config := {instances := true})
     [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc,
      MachineData.load, Width.bytes, Width.bits, Effects.All, all_if, ($hl), cast8,
      ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, BitVec.signed]
   simp only [instruction, next, put, putF, get, compare, subFlags,
     shift, low8, low32, replace8, Reg64s.set64, Reg64s.get64,
     BitVec.take, BitVec.drop, BitVec.replaceLow, BitVec.signed] at $hp:ident
   repeat' first | apply And.intro | intro
   all_goals try simp_all (config := {instances := true})
     [Effects.All, all_if, BitVec.ofInt_add, BitVec.ofInt_toInt,
      BitVec.take, BitVec.signed, BitVec.extractLsb'_append_eq_right,
      BitVec.add_comm, BitVec.add_assoc, UInt64.add_comm, UInt64.add_assoc]
   all_goals first
     | exact $hp ($s).status
     | exact $hp {($s).status with af := false}
     | exact $hp {($s).status with af := true}
     | exact $hp _))

/-- A one-instruction CPS certificate. Its continuation quantifies whole flags,
so using it repeatedly never duplicates a suffix for the undefined AF/OF choices.
The only assumptions about memory are ordinary mapped byte loads. -/
theorem instruction_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (pc : Nat) (hk : pc ∈ offsets) (s : MachineData) (b : BitVec 8)
    (hl : loads pc = true → Mem.loadInt s.dmem (address pc s) 1 = some (b.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (instruction pc s b flags, base + Int64.ofNat (next pc s))) :
    Eventually (step e) P (s, base + Int64.ofNat pc) := by
  have t2800 := hc.targets ("u2800", 2800) (by decide)
  have t2896 := hc.targets ("u2896", 2896) (by decide)
  have t5354 := hc.targets ("u5354", 5354) (by decide)
  have t5370 := hc.targets ("u5370", 5370) (by decide)
  have t5468 := hc.targets ("u5468", 5468) (by decide)
  have t5499 := hc.targets ("u5499", 5499) (by decide)
  simp [offsets, List.mem_cons] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  next =>
    uint_width_step 61 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 62 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 63 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 64 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 65 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 66 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 67 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 68 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 69 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 70 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 71 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 72 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 73 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 113 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 114 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 115 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 116 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 117 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 118 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 119 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 120 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 121 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 122 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 123 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 124 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 125 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 126 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 127 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 128 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 129 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 130 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 131 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 132 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 133 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 134 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 135 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 136 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 137 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 138 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 139 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 140 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 141 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 142 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 143 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 144 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 145 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 146 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 147 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 148 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 149 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 150 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 151 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 152 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 153 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 154 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 155 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 156 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 157 using hc
    uint_byte_finish s load hl cont hp
  next =>
    uint_width_step 158 using hc
    uint_byte_finish s load hl cont hp

end SszX86.UintCodec.Small
