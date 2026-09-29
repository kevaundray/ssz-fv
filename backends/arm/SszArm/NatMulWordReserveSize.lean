import SszArm.NatMulWordReserveHeader
import SszArm.NatFromU128LowerBase
import SszArm.NatCompareMemory
import SszArm.WordNormalize

namespace SszArm.NatMulWord.Reserve

inductive SizeGuard where
  | usize | multiply | bytes
  deriving DecidableEq

def SizeGuard.ops : SizeGuard → List Op
  | .usize => [.p320, .p324]
  | .multiply => [.p328, .p332, .p336]
  | .bytes => [.p340, .p344]

def SizeGuard.entry : SizeGuard → BitVec 64
  | .usize => 320 | .multiply => 328 | .bytes => 340

theorem size_run (guard : SizeGuard) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + guard.entry) :
    run guard.ops.length s = block base guard.ops s := by
  apply block_run base guard.ops s hc he ha
  have hpc : r .PC s = base + guard.entry := hp
  cases guard <;> simp [SizeGuard.ops, SizeGuard.entry, Follows, Op.row,
    Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules,
    hpc, BitVec.add_assoc]

theorem size_registers (guard : SizeGuard) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (keep : reg ≠ 10#5 ∧ reg ≠ 11#5) :
    r (.GPR reg) (block base guard.ops s) = r (.GPR reg) s := by
  apply block_preserves (r (.GPR reg)) base guard.ops
  intro op member t
  cases guard <;> simp only [SizeGuard.ops, List.mem_cons, List.not_mem_nil, or_false] at member
  case usize => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules, keep.1, keep.2]
  case multiply => rcases member with rfl | rfl | rfl <;>
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, keep.1, keep.2]
  case bytes => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules, keep.1, keep.2]

theorem size_frame (guard : SizeGuard) (s : ArmState) (base : BitVec 64) :
    Frame s (block base guard.ops s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    apply size_registers guard s base reg
    simp_all
  · intro reg
    exact block_preserves (r (.SFP reg)) base guard.ops (fun op _ t => op.sfp base t reg) s

theorem size_memory (guard : SizeGuard) (s : ArmState) (base : BitVec 64) :
    (block base guard.ops s).mem = s.mem := by
  apply block_preserves (fun t => t.mem) base guard.ops
  intro op member t
  cases guard <;> simp only [SizeGuard.ops, List.mem_cons, List.not_mem_nil, or_false] at member
  case usize => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case multiply => rcases member with rfl | rfl | rfl <;>
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  case bytes => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]

theorem Checkpoint.size {s t : ArmState} (reached : Checkpoint s t)
    (guard : SizeGuard) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + guard.entry) :
    Checkpoint s (block base guard.ops t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := size_run guard t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨⟨fuel + guard.ops.length, ?_⟩,
    reached.frame.trans (size_frame guard t base),
    (size_memory guard t base).trans reached.memory⟩
  rw [run_plus, hr, hrun]

theorem usize_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base SizeGuard.usize.ops s) =
      if (r (.GPR 9#5) s).toNat + 1 = 2^64 then base + 1632#64 else base + 328#64 := by
  have zero : (AddWithCarry (r (.GPR 9#5) s) 1#64 0#1).2.z = 1#1 ↔
      (r (.GPR 9#5) s).toNat + 1 = 2^64 := by
    change (if (AddWithCarry (r (.GPR 9#5) s) 1#64 0#1).1 = 0#64
      then 1#1 else 0#1) = 1#1 ↔ _
    rw [Udivti3.adc_value]
    simp only [BitVec.setWidth_zero, BitVec.add_zero]
    by_cases sum : r (.GPR 9#5) s + 1#64 = 0#64 <;> simp [sum] <;> bv_omega
  simp [block, SizeGuard.ops, Op.effect, next, state_simp_rules, zero]

theorem multiply_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base SizeGuard.multiply.ops s) =
      if 2305843009213693950 < (r (.GPR 9#5) s).toNat
        then base + 1264#64 else base + 340#64 := by
  have comparison := Udivti3.cmp_high (r (.GPR 9#5) s) 2305843009213693950#64
  have complement : ~~~(2305843009213693950#64) = 16140901064495857665#64 := by decide
  rw [complement] at comparison
  simp only [BitVec.toNat_ofNat] at comparison
  simp [block, SizeGuard.ops, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, comparison]
theorem bytes_exit (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 340#64)
    (bound : (r (.GPR 9#5) s).toNat ≤ 2305843009213693950) :
    read_pc (block base SizeGuard.bytes.ops s) = base + 348#64 ∧
      (r (.GPR 11#5) (block base SizeGuard.bytes.ops s)).toNat =
        8 * ((r (.GPR 9#5) s).toNat + 1) := by
  have hpc : r .PC s = base + 340#64 := hp
  constructor
  · simp [block, SizeGuard.ops, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  · have value : r (.GPR 11#5) (block base SizeGuard.bytes.ops s) =
        (r (.GPR 9#5) s <<< 3) + 8#64 := by
      simp only [block, SizeGuard.ops, List.foldl_cons, List.foldl_nil, Op.effect, put, next]
      arm_state_nf
    rw [value]
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega

def signOps (negative : Bool) : List Op :=
  [.p348, .p352, .p356, .p360] ++
    if negative then [.p376, .p380, .p384] else [.p364, .p368, .p372]

def signMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s

def signTailOps (negative : Bool) : List Op :=
  [.p356, .p360] ++
    if negative then [.p376, .p380, .p384] else [.p364, .p368, .p372]

theorem sign_split (negative : Bool) (s : ArmState) (base : BitVec 64) :
    block base (signOps negative) s =
      block base (signTailOps negative) (block base [.p348, .p352] s) := by
  cases negative <;> rfl

theorem sign_tail_nine (negative : Bool) (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base (signTailOps negative) s) =
      read_mem_bytes 8 (r (.GPR 31#5) s) s := by
  cases negative <;>
    simp [signTailOps, block, Op.effect, put, next, state_simp_rules]

theorem sign_tail_sp (negative : Bool) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base (signTailOps negative) s) = r (.GPR 31#5) s + 16#64 := by
  cases negative <;>
    simp [signTailOps, block, Op.effect, put, next, state_simp_rules]

theorem sign_tail_memory (negative : Bool) (s : ArmState) (base : BitVec 64) :
    (block base (signTailOps negative) s).mem = s.mem := by
  apply block_preserves (fun t => t.mem) base (signTailOps negative)
  intro op member t
  cases negative <;>
    simp only [signTailOps, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]

theorem sign_tail_pc (negative : Bool) (s : ArmState) (base : BitVec 64) :
    read_pc (block base (signTailOps negative) s) =
      base + (if negative then 1264#64 else 388#64) := by
  cases negative
  · change r .PC (w .PC (base + 388#64) _) = base + 388#64
    rw [r_of_w_same]
  · change r .PC (w .PC (base + 1264#64) _) = base + 1264#64
    rw [r_of_w_same]

theorem sign_run (negative : Bool) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 348#64)
    (selected : ((r (.GPR 11#5) s &&& 9223372036854775808#64) = 0#64) ↔ negative = false) :
    run 7 s = block base (signOps negative) s := by
  have hpc : r .PC s = base + 348#64 := hp
  have length : (signOps negative).length = 7 := by cases negative <;> rfl
  rw [← length]
  apply block_run base (signOps negative) s hc he ha
  cases negative <;> simp_all [signOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, BitVec.add_assoc]

theorem sign_registers (negative : Bool) (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5) :
    r (.GPR reg) (block base (signOps negative) s) = r (.GPR reg) s := by
  have slot : (r (.GPR 31#5) s - 16#64).toNat + 8 ≤ 2^64 := by bv_omega
  by_cases nine : reg = 9#5
  · subst reg
    rw [sign_split, sign_tail_nine]
    simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next]
    arm_state_nf
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ slot
  by_cases sp : reg = 31#5
  · subst reg
    rw [sign_split, sign_tail_sp]
    simp [block, Op.effect, put, next, state_simp_rules, BitVec.sub_add_cancel]
  apply block_preserves (r (.GPR reg)) base (signOps negative)
  intro op member t
  cases negative <;>
    simp only [signOps, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules, nine, sp]

theorem sign_effect (negative : Bool) (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    let t := block base (signOps negative) s
    Frame s t ∧ t.mem = (signMemory s).mem ∧
      r (.GPR 11#5) t = r (.GPR 11#5) s ∧
      read_pc t = base + (if negative then 1264#64 else 388#64) := by
  have regs := sign_registers negative s base stack
  refine ⟨⟨block_program _ _ _, block_error _ _ _, fun reg _ => regs reg, ?_⟩, ?_, regs _, ?_⟩
  · intro reg
    exact block_preserves (r (.SFP reg)) base (signOps negative)
      (fun op _ t => op.sfp base t reg) s
  · rw [sign_split, sign_tail_memory]
    simp [signMemory, block, Op.effect, put, next, state_simp_rules, NatCompare.spill_mem_w]
  · rw [sign_split, sign_tail_pc]

theorem sign_memory_frame (s : ArmState) (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 8)] s (signMemory s) := by
  intro a outside
  have address : (r (.GPR 31#5) s - 16#64).toNat = (r (.GPR 31#5) s).toNat - 16 := by bv_omega
  apply BoolCodec.write_mem_bytes_frame _ _ _ _ a (by bv_omega)
  simpa only [address] using outside ((r (.GPR 31#5) s).toNat - 16, 8) (by simp)

end SszArm.NatMulWord.Reserve
