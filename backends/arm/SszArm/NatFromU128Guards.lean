import SszArm.NatFromU128Exec
import SszArm.DelimitedArenaArithmetic

namespace SszArm.NatFromU128

structure GuardFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem GuardFrame.refl (s : ArmState) : GuardFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem GuardFrame.trans {s t u : ArmState} (st : GuardFrame s t)
    (tu : GuardFrame t u) : GuardFrame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem GuardFrame.sp {s t : ArmState} (frame : GuardFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem GuardFrame.aligned {s t : ArmState} (frame : GuardFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem GuardFrame.code {s t : ArmState} (frame : GuardFrame s t)
    (base : BitVec 64) (hc : CodeAt s base) : CodeAt t base := by
  intro row hr
  simpa only [frame.program] using hc row hr

inductive CheckKind where
  | address | round | align | finish | capacity
  deriving DecidableEq

def CheckKind.ops : CheckKind → List Op
  | .address => [.p88, .p92, .p96, .p100]
  | .round => [.p104, .p108]
  | .align => [.p112, .p116, .p120, .p124, .p128]
  | .finish => [.p132, .p136]
  | .capacity => [.p140, .p144, .p148, .p152]

def CheckKind.entry : CheckKind → BitVec 64
  | .address => 88#64
  | .round => 104#64
  | .align => 112#64
  | .finish => 132#64
  | .capacity => 140#64

def CheckKind.clobbers : CheckKind → List (BitVec 5)
  | .address => [8#5, 9#5, 10#5]
  | .round => []
  | .align => [10#5, 11#5]
  | .finish => []
  | .capacity => [8#5, 11#5]

theorem guard_registers (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) (reg : BitVec 5) (hr : reg ∉ kind.clobbers) :
    r (.GPR reg) (block base kind.ops s) = r (.GPR reg) s := by
  cases kind <;> simp only [CheckKind.clobbers, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hr <;>
    simp (disch := simp_all) [CheckKind.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_frame (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) : GuardFrame s (block base kind.ops s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    apply guard_registers kind s base reg
    cases kind <;> simp_all [CheckKind.clobbers]
  · intro reg
    cases kind <;> simp [CheckKind.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_memory (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) : (block base kind.ops s).mem = s.mem := by
  cases kind <;> simp [CheckKind.ops, block, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_run (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + kind.entry) :
    run kind.ops.length s = block base kind.ops s := by
  apply block_run base kind.ops s hc he ha
  have hpc : r .PC s = base + kind.entry := hp
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [CheckKind.ops, CheckKind.entry, Follows, Op.row, Op.effect, put, next,
       Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

structure Checkpoint (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : GuardFrame s t
  memory : t.mem = s.mem

theorem Checkpoint.refl (s : ArmState) : Checkpoint s s :=
  ⟨⟨0, rfl⟩, GuardFrame.refl s, rfl⟩

theorem Checkpoint.step {s t : ArmState} (reached : Checkpoint s t)
    (kind : CheckKind) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + kind.entry) :
    Checkpoint s (block base kind.ops t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := guard_run kind t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨⟨fuel + kind.ops.length, ?_⟩,
    reached.frame.trans (guard_frame kind t base),
    (guard_memory kind t base).trans reached.memory⟩
  rw [run_plus, hr, hrun]

theorem Checkpoint.header {s t : ArmState} (reached : Checkpoint s t)
    (offset : BitVec 64) :
    read_mem_bytes 8 (r (.GPR 4#5) t + offset) t =
      read_mem_bytes 8 (r (.GPR 4#5) s + offset) s := by
  rw [reached.frame.registers 4#5 (by decide)]
  exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.memory _ _

private theorem cmn_hi_zero (a b : BitVec 64) :
    ((AddWithCarry a b 0#1).2.c = 1#1 ∧ (AddWithCarry a b 0#1).2.z = 0#1) ↔
      2^64 < a.toNat + b.toNat := by
  have hz : (AddWithCarry a b 0#1).2.z = 0#1 ↔
      (AddWithCarry a b 0#1).2.z ≠ 1#1 := by bv_omega
  rw [hz]
  exact Delimited.cmn_hi a b

theorem address_exit (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 4#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s
    let t := block base CheckKind.address.ops s
    r (.GPR 9#5) t = pointer ∧ r (.GPR 8#5) t = used ∧
      r (.GPR 10#5) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 220#64 else base + 104#64 := by
  simp [block, CheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem round_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base CheckKind.round.ops s) =
      if 2^64 < (r (.GPR 10#5) s).toNat + 8 then base + 220#64 else base + 112#64 := by
  simp [block, CheckKind.ops, Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem align_exit (s : ArmState) (base : BitVec 64) :
    let aligned := (r (.GPR 10#5) s + 7#64) &&& 18446744073709551608#64
    let padding := aligned - r (.GPR 10#5) s
    let t := block base CheckKind.align.ops s
    r (.GPR 11#5) t = aligned ∧
      r (.GPR 10#5) t = padding + r (.GPR 8#5) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 8#5) s).toNat
        then base + 220#64 else base + 132#64 := by
  simp [block, CheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem finish_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base CheckKind.finish.ops s) =
      if 2^64 < (r (.GPR 10#5) s).toNat + 17 then base + 220#64 else base + 140#64 := by
  simp [block, CheckKind.ops, Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem capacity_exit (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
    let finish := r (.GPR 10#5) s + 16#64
    let t := block base CheckKind.capacity.ops s
    r (.GPR 8#5) t = capacity ∧ r (.GPR 11#5) t = finish ∧
      read_pc t = if capacity.toNat < finish.toNat
        then base + 220#64 else base + 156#64 := by
  simp [block, CheckKind.ops, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, Udivti3.cmp_high]

end SszArm.NatFromU128
