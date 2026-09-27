import SszArm.MemmoveMemory

/-!
Complete overlap-safe ARM memmove. The forward block is the checked memcpy
instruction sequence embedded here, not a call to an external function. Its
memory proof uses ordering, not memcpy's disjointness precondition. The backward
block loads each entire vector before storing, then handles the exact byte tail.
The code map is immutable and independent of total ordinary byte memory;
mappings, permissions, devices, alignment traps and concurrent interference are
outside this model. Empty and equal-pointer paths execute RET without data access.
-/
namespace SszArm.Memmove

open BitVec

/-- Literal A64 words in assembly order. Branch immediates are word offsets;
backward loads/stores use supported signed post-index imm9 encodings. -/
def program : List (BitVec 32) :=
  [0xb4000242#32, 0xcb010004#32, 0xb4000204#32, 0xeb01001f#32,
   0x540001e2#32,
   0xaa0003e3#32, 0xf100405f#32, 0x540000c3#32, 0x3cc10420#32,
   0x3c810460#32, 0xd1004042#32, 0xf100405f#32, 0x54ffff82#32,
   0xb40000a2#32, 0x38401424#32, 0x38001464#32, 0xd1000442#32,
   0xb5ffffa2#32, 0xd65f03c0#32,
   0x8b020021#32, 0x8b020003#32, 0xf100405f#32, 0x54000183#32,
   0xd1004021#32, 0xd1004063#32, 0x3cdf0420#32, 0x3c9f0460#32,
   0xd1004042#32, 0xf100405f#32, 0x54ffff82#32, 0xb4000142#32,
   0x91003c21#32, 0x91003c63#32, 0x14000003#32,
   0xd1000421#32, 0xd1000463#32, 0x385ff424#32, 0x381ff464#32,
   0xd1000442#32, 0xb5ffffa2#32, 0xd65f03c0#32]

/-- The five-instruction dispatcher has no data-memory operation. -/
def dispatch_instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 72#64
      else read_pc s + 4#64) s
  | 1 => w .PC (read_pc s + 4#64)
      (w (.GPR 4) (r (.GPR 0) s - r (.GPR 1) s) s)
  | 2 => w .PC (if r (.GPR 4) s = 0#64 then read_pc s + 64#64
      else read_pc s + 4#64) s
  | 3 => write_pstate (AddWithCarry (r (.GPR 0) s) (~~~r (.GPR 1) s) 1#1).2
      (w .PC (read_pc s + 4#64) s)
  | 4 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s + 60#64) s
      else w .PC (read_pc s + 4#64) s
  | _ => s

def equal_entry (s : ArmState) : ArmState :=
  dispatch_instruction 2 (dispatch_instruction 1 (dispatch_instruction 0 s))

def dispatch (s : ArmState) : ArmState :=
  dispatch_instruction 4 (dispatch_instruction 3 (equal_entry s))

def return_state (s : ArmState) : ArmState := w .PC (r (.GPR 30) s) s

abbrev Preserved := SszArm.Memcpy.Preserved

/-- The selected terminating state; every branch is subsequently related to run. -/
def result (s : ArmState) : ArmState :=
  if r (.GPR 2) s = 0#64 then return_state (dispatch_instruction 0 s)
  else if r (.GPR 0) s = r (.GPR 1) s then return_state (equal_entry s)
  else if (r (.GPR 0) s).toNat < (r (.GPR 1) s).toNat then SszArm.Memcpy.result (dispatch s)
  else Backward.result (dispatch s)

/-- Exact number of executed instructions, including RET on all paths. -/
def fuel (s : ArmState) : Nat :=
  if r (.GPR 2) s = 0#64 then 2
  else if r (.GPR 0) s = r (.GPR 1) s then 4
  else if (r (.GPR 0) s).toNat < (r (.GPR 1) s).toNat
    then 5 + SszArm.Memcpy.fuel (r (.GPR 2) s).toNat
    else 5 + Backward.fuel (r (.GPR 2) s).toNat

private theorem wide_add_nat (x y : BitVec 64) (c : BitVec 1) :
    (x.setWidth 65 + y.setWidth 65 + c.setWidth 65).toNat =
      x.toNat + y.toNat + c.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc := c.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 65),
    BitVec.toNat_setWidth_of_le (by decide : 1 ≤ 65)]
  have hxy : x.toNat + y.toNat < 2^65 := by omega
  rw [Nat.mod_eq_of_lt hxy]
  exact Nat.mod_eq_of_lt (by omega)

/-- The dispatcher uses the actual carry flag of unsigned subtraction. -/
theorem carry_compare (x y : BitVec 64) :
    (AddWithCarry x (~~~y) 1#1).2.c = 1#1 ↔ y.toNat ≤ x.toNat := by
  let u : BitVec 65 := x.setWidth 65 + (~~~y).setWidth 65 + (1#1).setWidth 65
  have hy := y.isLt
  have hx := x.isLt
  have hu : u.toNat = x.toNat + (2^64 - 1 - y.toNat) + 1 := by
    dsimp only [u]
    rw [wide_add_nat, BitVec.toNat_not, BitVec.toNat_ofNat]
  have hc : (u.setWidth 64 |>.setWidth 65) = u ↔ x.toNat < y.toNat := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth] at hn
      rw [hu] at hn
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      rw [hu]
      omega
  simp only [AddWithCarry, make_pstate]
  change (if (u.setWidth 64 |>.setWidth 65) = u then 0#1 else 1#1) = 1#1 ↔ _
  by_cases h : (u.setWidth 64 |>.setWidth 65) = u
  · rw [if_pos h]
    have hn := hc.mp h
    have hz : (0#1 : BitVec 1) ≠ 1#1 := by decide
    exact ⟨fun he => False.elim (hz he), fun he => False.elim ((Nat.not_le_of_lt hn) he)⟩
  · rw [if_neg h]
    have hn : y.toNat ≤ x.toNat := Nat.le_of_not_gt (fun hn => h (hc.mpr hn))
    exact ⟨fun _ => hn, fun _ => rfl⟩

theorem dispatch_instruction_frame (k : Nat) (s : ArmState) (f : StateField)
    (h : Preserved f) : r f (dispatch_instruction k s) = r f s := by
  cases f <;> simp only [Preserved, SszArm.Memcpy.Preserved] at h
  · rcases h with ⟨h1, h2, h3, h4⟩
    unfold dispatch_instruction
    split <;> simp [state_simp_rules, h4, apply_ite]
  · unfold dispatch_instruction
    split <;> simp [state_simp_rules, apply_ite]
  · unfold dispatch_instruction
    split <;> simp [state_simp_rules, apply_ite]

theorem dispatch_instruction_program (k : Nat) (s : ArmState) :
    (dispatch_instruction k s).program = s.program := by
  unfold dispatch_instruction
  split <;> simp [state_simp_rules, apply_ite]

theorem dispatch_instruction_err (k : Nat) (s : ArmState) :
    read_err (dispatch_instruction k s) = read_err s :=
  dispatch_instruction_frame k s .ERR trivial

theorem dispatch_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (dispatch s) = r f s := by
  simp only [dispatch, equal_entry, dispatch_instruction_frame _ _ _ h]

theorem dispatch_program (s : ArmState) : (dispatch s).program = s.program := by
  simp only [dispatch, equal_entry, dispatch_instruction_program]

theorem dispatch_data (s : ArmState) :
    (dispatch s).mem = s.mem ∧
    r (.GPR 0) (dispatch s) = r (.GPR 0) s ∧
    r (.GPR 1) (dispatch s) = r (.GPR 1) s ∧
    r (.GPR 2) (dispatch s) = r (.GPR 2) s := by
  simp [dispatch, equal_entry, dispatch_instruction, state_simp_rules, apply_ite]

end SszArm.Memmove
