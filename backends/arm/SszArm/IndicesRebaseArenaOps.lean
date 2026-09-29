import SszArm.IndicesLinkedRebase
import SszArm.NatCompareMemory
import SszArm.DelimitedArenaArithmetic
import SszArm.DelimitedMemory

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Arena

inductive Op where
  | p604 | p608 | p612 | p616 | p620 | p624 | p628 | p632 | p636 | p640
  | p644 | p648 | p652 | p656 | p660 | p664 | p668 | p672 | p676 | p680
  | p684 | p688 | p692 | p696 | p700 | p704 | p708 | p712 | p716 | p720
  | p724 | p728 | p732 | p736 | p740 | p744
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p604 => (604, 0xd37dfd4b#32)
  | .p608 => (608, 0xb500046b#32)
  | .p612 => (612, 0xd37df14c#32)
  | .p616 => (616, 0xd10043ff#32)
  | .p620 => (620, 0xf90003e9#32)
  | .p624 => (624, 0x92410189#32)
  | .p628 => (628, 0xb5000089#32)
  | .p632 => (632, 0xf94003e9#32)
  | .p636 => (636, 0x910043ff#32)
  | .p640 => (640, 0x14000004#32)
  | .p644 => (644, 0xf94003e9#32)
  | .p648 => (648, 0x910043ff#32)
  | .p652 => (652, 0x14000018#32)
  | .p656 => (656, 0xf94000cb#32)
  | .p660 => (660, 0xf94008cd#32)
  | .p664 => (664, 0xab0b01ae#32)
  | .p668 => (668, 0x54000282#32)
  | .p672 => (672, 0xb10021df#32)
  | .p676 => (676, 0x54000248#32)
  | .p680 => (680, 0x91001dcf#32)
  | .p684 => (684, 0x927df1ef#32)
  | .p688 => (688, 0xcb0e01ee#32)
  | .p692 => (692, 0xab0d01cd#32)
  | .p696 => (696, 0x540001a2#32)
  | .p700 => (700, 0xab0c01ac#32)
  | .p704 => (704, 0x54000162#32)
  | .p708 => (708, 0xf94004ce#32)
  | .p712 => (712, 0xeb0e019f#32)
  | .p716 => (716, 0x54000108#32)
  | .p720 => (720, 0x8b0d016b#32)
  | .p724 => (724, 0xaa0203ee#32)
  | .p728 => (728, 0xf90008cc#32)
  | .p732 => (732, 0xb40006e1#32)
  | .p736 => (736, 0xb40006a2#32)
  | .p740 => (740, 0xf940002e#32)
  | .p744 => (744, 0x14000034#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p604, s => put 11 (r (.GPR 10#5) s >>> 61) s
  | .p608, s => w .PC (if r (.GPR 11#5) s = 0#64 then base + 612#64 else base + 748#64) s
  | .p612, s => put 12 (r (.GPR 10#5) s <<< 3) s
  | .p616, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p620, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p624, s => put 9 (r (.GPR 12#5) s &&& 9223372036854775808#64) s
  | .p628, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 632#64 else base + 644#64) s
  | .p632, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p636, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p640, s => w .PC (base + 656#64) s
  | .p644, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p648, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p652, s => w .PC (base + 748#64) s
  | .p656, s => put 11 (read_mem_bytes 8 (r (.GPR 6#5) s) s) s
  | .p660, s => put 13 (read_mem_bytes 8 (r (.GPR 6#5) s + 16#64) s) s
  | .p664, s => write_pstate (AddWithCarry (r (.GPR 13#5) s) (r (.GPR 11#5) s) 0#1).2
      (put 14 (r (.GPR 13#5) s + r (.GPR 11#5) s) s)
  | .p668, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 748#64 else base + 672#64) s
  | .p672, s => write_pstate (AddWithCarry (r (.GPR 14#5) s) 8#64 0#1).2 (next s)
  | .p676, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 748#64 else base + 680#64) s
  | .p680, s => put 15 (r (.GPR 14#5) s + 7#64) s
  | .p684, s => put 15 (r (.GPR 15#5) s &&& 18446744073709551608#64) s
  | .p688, s => put 14 (r (.GPR 15#5) s - r (.GPR 14#5) s) s
  | .p692, s => write_pstate (AddWithCarry (r (.GPR 14#5) s) (r (.GPR 13#5) s) 0#1).2
      (put 13 (r (.GPR 14#5) s + r (.GPR 13#5) s) s)
  | .p696, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 748#64 else base + 700#64) s
  | .p700, s => write_pstate (AddWithCarry (r (.GPR 13#5) s) (r (.GPR 12#5) s) 0#1).2
      (put 12 (r (.GPR 13#5) s + r (.GPR 12#5) s) s)
  | .p704, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 748#64 else base + 708#64) s
  | .p708, s => put 14 (read_mem_bytes 8 (r (.GPR 6#5) s + 8#64) s) s
  | .p712, s => Udivti3.compare (r (.GPR 12#5) s) (r (.GPR 14#5) s) s
  | .p716, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 748#64 else base + 720#64) s
  | .p720, s => put 11 (r (.GPR 11#5) s + r (.GPR 13#5) s) s
  | .p724, s => put 14 (r (.GPR 2#5) s) s
  | .p728, s => next (write_mem_bytes 8 (r (.GPR 6#5) s + 16#64) (r (.GPR 12#5) s) s)
  | .p732, s => w .PC (if r (.GPR 1#5) s = 0#64 then base + 952#64 else base + 736#64) s
  | .p736, s => w .PC (if r (.GPR 2#5) s = 0#64 then base + 948#64 else base + 740#64) s
  | .p740, s => put 14 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p744, s => w .PC (base + 952#64) s

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : Linked.Rebase.CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hm : op.row ∈ Linked.Rebase.chunk2 := by cases op <;> decide
  have hf := Linked.Rebase.chunk2_codeAt hc op.row hm
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by
    have h := (r (.FLAG .Z) s).isLt
    rw [← BitVec.toNat_inj, ← BitVec.toNat_inj]
    simp only [BitVec.toNat_ofNat] at *
    omega
  cases op
  all_goals
    simp only [Op.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, Udivti3.compare, Udivti3.next,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, ha, hp, BitVec.add_assoc, apply_ite, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

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
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hc : Linked.Rebase.CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [Linked.Rebase.CodeAt, Codec.Linked.WordsAt, Op.program] using hc)
      (by simpa only [Op.error] using he) (op.aligned base s ha) hf.2

theorem block_preserves {α : Sort _} (observe : ArmState → α) (base : BitVec 64)
    (ops : List Op) (preserves : ∀ op ∈ ops, ∀ s, observe (op.effect base s) = observe s)
    (s : ArmState) : observe (block base ops s) = observe s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (fun q member => preserves q (List.mem_cons_of_mem _ member)) _).trans
      (preserves op (by simp) s)

@[simp] theorem block_program (base : BitVec 64) (ops : List Op) (s : ArmState) :
    (block base ops s).program = s.program :=
  block_preserves (fun t => t.program) base ops (fun op _ t => op.program base t) s

@[simp] theorem block_error (base : BitVec 64) (ops : List Op) (s : ArmState) :
    read_err (block base ops s) = read_err s :=
  block_preserves read_err base ops (fun op _ t => op.error base t) s

theorem block_vectors (base : BitVec 64) (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block base ops s) = r (.SFP reg) s :=
  block_preserves (r (.SFP reg)) base ops (fun op _ t => op.sfp base t reg) s

structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [11#5, 12#5, 13#5, 14#5, 15#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Frame.trans {s t u : ArmState} (st : Frame s t) (tu : Frame t u) : Frame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem Frame.sp {s t : ArmState} (h : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem Frame.aligned {s t : ArmState} (h : Frame s t) (ha : CheckSPAlignment s) :
    CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem Frame.code {s t : ArmState} (h : Frame s t) (base : BitVec 64)
    (hc : Linked.Rebase.CodeAt s base) : Linked.Rebase.CodeAt t base := by
  intro row member
  simpa only [h.program] using hc row member

end SszArm.Indices.Rebase.Arena
