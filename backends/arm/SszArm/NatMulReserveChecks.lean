import SszArm.NatMulExec
import SszArm.DelimitedArenaArithmetic

namespace SszArm.NatMul


/-- Reservation guards only clobber the four caller-saved scratch registers. -/
structure ReserveFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [10#5, 11#5, 12#5, 13#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem ReserveFrame.refl (s : ArmState) : ReserveFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem ReserveFrame.trans {s t u : ArmState} (st : ReserveFrame s t)
    (tu : ReserveFrame t u) : ReserveFrame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem ReserveFrame.sp {s t : ArmState} (frame : ReserveFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem ReserveFrame.aligned {s t : ArmState} (frame : ReserveFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem ReserveFrame.code {s t : ArmState} (frame : ReserveFrame s t)
    (base : BitVec 64) (hc : CodeAt s base) : CodeAt t base := by
  intro row hr
  simpa only [frame.program] using hc row hr

inductive ReserveCheckKind where
  | address | round | align | finish | capacity
  deriving DecidableEq

def ReserveCheckKind.ops : ReserveCheckKind → List Op
  | .address => [.p472, .p476, .p480, .p484]
  | .round => [.p488, .p492]
  | .align => [.p496, .p500, .p504, .p508, .p512]
  | .finish => [.p516, .p520]
  | .capacity => [.p524, .p528, .p532]

def ReserveCheckKind.entry : ReserveCheckKind → BitVec 64
  | .address => 472#64
  | .round => 488#64
  | .align => 496#64
  | .finish => 516#64
  | .capacity => 524#64

def ReserveCheckKind.clobbers : ReserveCheckKind → List (BitVec 5)
  | .address => [10#5, 11#5, 12#5]
  | .round => []
  | .align => [13#5, 11#5, 12#5]
  | .finish => [12#5]
  | .capacity => [13#5]

/-- State-independent observations compose without expanding nested machine states. -/
theorem reserve_block_preserves {α : Sort _} (observe : ArmState → α)
    (base : BitVec 64) (ops : List Op)
    (one : ∀ op ∈ ops, ∀ s, observe (op.effect base s) = observe s)
    (s : ArmState) : observe (block base ops s) = observe s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change observe (block base ops (op.effect base s)) = observe s
    exact (ih (fun p hp => one p (List.mem_cons_of_mem op hp)) _).trans
      (one op (List.mem_cons_self) s)

private theorem reserve_one_register (kind : ReserveCheckKind) (op : Op)
    (member : op ∈ kind.ops) (base : BitVec 64) (reg : BitVec 5)
    (hr : reg ∉ kind.clobbers) (s : ArmState) :
    r (.GPR reg) (op.effect base s) = r (.GPR reg) s := by
  cases kind <;>
    simp only [ReserveCheckKind.ops, List.mem_cons, List.not_mem_nil, or_false] at member
  case address => rcases member with rfl | rfl | rfl | rfl <;>
    simp_all [ReserveCheckKind.clobbers, Op.effect, put, next, state_simp_rules]
  case round => rcases member with rfl | rfl <;>
    simp_all [ReserveCheckKind.clobbers, Op.effect, put, next, state_simp_rules]
  case align => rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [ReserveCheckKind.clobbers, Op.effect, put, next, state_simp_rules]
  case finish => rcases member with rfl | rfl <;>
    simp_all [ReserveCheckKind.clobbers, Op.effect, put, next, state_simp_rules]
  case capacity => rcases member with rfl | rfl | rfl <;>
    simp_all [ReserveCheckKind.clobbers, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules]

theorem reserve_guard_registers (kind : ReserveCheckKind) (s : ArmState)
    (base : BitVec 64) (reg : BitVec 5) (hr : reg ∉ kind.clobbers) :
    r (.GPR reg) (block base kind.ops s) = r (.GPR reg) s :=
  reserve_block_preserves (r (.GPR reg)) base kind.ops
    (fun op member t => reserve_one_register kind op member base reg hr t) s

theorem reserve_guard_frame (kind : ReserveCheckKind) (s : ArmState)
    (base : BitVec 64) : ReserveFrame s (block base kind.ops s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    apply reserve_guard_registers kind s base reg
    cases kind <;> simp_all [ReserveCheckKind.clobbers]
  · intro reg
    exact reserve_block_preserves (r (.SFP reg)) base kind.ops
      (fun op _ t => op.sfp base t reg) s

theorem reserve_guard_memory (kind : ReserveCheckKind) (s : ArmState)
    (base : BitVec 64) : (block base kind.ops s).mem = s.mem := by
  apply reserve_block_preserves (fun t => t.mem) base kind.ops
  intro op member t
  cases kind <;>
    simp only [ReserveCheckKind.ops, List.mem_cons, List.not_mem_nil, or_false] at member
  case address => rcases member with rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case round => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case align => rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case finish => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case capacity => rcases member with rfl | rfl | rfl <;>
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem reserve_guard_run (kind : ReserveCheckKind) (s : ArmState)
    (base : BitVec 64) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + kind.entry) :
    run kind.ops.length s = block base kind.ops s := by
  apply block_run base kind.ops s hc he ha
  have hpc : r .PC s = base + kind.entry := hp
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [ReserveCheckKind.ops, ReserveCheckKind.entry, Follows, Op.row, Op.effect, put, next,
       Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

/-- Read-only guard prefixes compose actual runs and preserve the arena header. -/
structure ReserveCheckpoint (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : ReserveFrame s t
  memory : t.mem = s.mem

theorem ReserveCheckpoint.refl (s : ArmState) : ReserveCheckpoint s s :=
  ⟨⟨0, rfl⟩, ReserveFrame.refl s, rfl⟩

theorem ReserveCheckpoint.step {s t : ArmState} (reached : ReserveCheckpoint s t)
    (kind : ReserveCheckKind) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + kind.entry) :
    ReserveCheckpoint s (block base kind.ops t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := reserve_guard_run kind t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨⟨fuel + kind.ops.length, ?_⟩,
    reached.frame.trans (reserve_guard_frame kind t base),
    (reserve_guard_memory kind t base).trans reached.memory⟩
  rw [run_plus, hr, hrun]

theorem ReserveCheckpoint.header {s t : ArmState} (reached : ReserveCheckpoint s t)
    (offset : BitVec 64) :
    read_mem_bytes 8 (r (.GPR 5#5) t + offset) t =
      read_mem_bytes 8 (r (.GPR 5#5) s + offset) s := by
  rw [reached.frame.registers 5#5 (by decide)]
  exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.memory _ _

private theorem cmn_hi_zero (a b : BitVec 64) :
    ((AddWithCarry a b 0#1).2.c = 1#1 ∧ (AddWithCarry a b 0#1).2.z = 0#1) ↔
      2^64 < a.toNat + b.toNat := by
  have hz : (AddWithCarry a b 0#1).2.z = 0#1 ↔
      (AddWithCarry a b 0#1).2.z ≠ 1#1 := by bv_omega
  rw [hz]
  exact Delimited.cmn_hi a b

theorem reserve_address_exit (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 5#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s
    let t := block base ReserveCheckKind.address.ops s
    r (.GPR 10#5) t = pointer ∧ r (.GPR 11#5) t = used ∧
      r (.GPR 12#5) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 1076#64 else base + 488#64 := by
  simp [block, ReserveCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem reserve_round_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base ReserveCheckKind.round.ops s) =
      if 2^64 < (r (.GPR 12#5) s).toNat + 8 then base + 1076#64 else base + 496#64 := by
  simp [block, ReserveCheckKind.ops, Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem reserve_align_exit (s : ArmState) (base : BitVec 64) :
    let aligned := (r (.GPR 12#5) s + 7#64) &&& 18446744073709551608#64
    let padding := aligned - r (.GPR 12#5) s
    let t := block base ReserveCheckKind.align.ops s
    r (.GPR 13#5) t = aligned ∧ r (.GPR 12#5) t = padding ∧
      r (.GPR 11#5) t = padding + r (.GPR 11#5) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 11#5) s).toNat
        then base + 1076#64 else base + 516#64 := by
  simp [block, ReserveCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem reserve_end_exit (s : ArmState) (base : BitVec 64) :
    let t := block base ReserveCheckKind.finish.ops s
    r (.GPR 12#5) t = r (.GPR 11#5) s + r (.GPR 2#5) s ∧
      read_pc t = if 2^64 ≤ (r (.GPR 11#5) s).toNat + (r (.GPR 2#5) s).toNat
        then base + 1076#64 else base + 524#64 := by
  simp [block, ReserveCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem reserve_capacity_exit (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s
    let t := block base ReserveCheckKind.capacity.ops s
    r (.GPR 13#5) t = capacity ∧
      read_pc t = if capacity.toNat < (r (.GPR 12#5) s).toNat
        then base + 1076#64 else base + 536#64 := by
  simp [block, ReserveCheckKind.ops, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, Udivti3.cmp_high]

end SszArm.NatMul
