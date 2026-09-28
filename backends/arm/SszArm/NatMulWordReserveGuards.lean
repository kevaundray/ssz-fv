import SszArm.NatMulWordExec
import SszArm.DelimitedArenaArithmetic

namespace SszArm.NatMulWord.Reserve

inductive Width where
  | wide | large
  deriving DecidableEq

inductive Guard where
  | address | round | align | finish | capacity
  deriving DecidableEq

def Width.startReg : Width → BitVec 5 | .wide => 11 | .large => 16
def Width.usedReg : Width → BitVec 5 | .wide => 11 | .large => 13
def Width.addressReg : Width → BitVec 5 | .wide => 12 | .large => 14
def Width.alignedReg : Width → BitVec 5 | .wide => 13 | .large => 15
def Width.finishReg : Width → BitVec 5 | .wide => 12 | .large => 17

def Width.bytes (width : Width) (s : ArmState) : BitVec 64 :=
  match width with | .wide => 16#64 | .large => r (.GPR 11#5) s

def Width.endValue (width : Width) (s : ArmState) : BitVec 64 :=
  match width with | .wide => r (.GPR 11#5) s + 16#64 | .large => r (.GPR 17#5) s

def Guard.ops : Width → Guard → List Op
  | .wide, .address => [.p1132, .p1136, .p1140, .p1144]
  | .wide, .round => [.p1148, .p1152]
  | .wide, .align => [.p1156, .p1160, .p1164, .p1168, .p1172]
  | .wide, .finish => [.p1176, .p1180]
  | .wide, .capacity => [.p1184, .p1188, .p1192, .p1196]
  | .large, .address => [.p388, .p392, .p396, .p400]
  | .large, .round => [.p404, .p408]
  | .large, .align => [.p412, .p416, .p420, .p424, .p428]
  | .large, .finish => [.p432, .p436]
  | .large, .capacity => [.p440, .p444, .p448]

def Guard.entry : Width → Guard → BitVec 64
  | .wide, .address => 1132 | .wide, .round => 1148 | .wide, .align => 1156
  | .wide, .finish => 1176 | .wide, .capacity => 1184
  | .large, .address => 388 | .large, .round => 404 | .large, .align => 412
  | .large, .finish => 432 | .large, .capacity => 440

def Width.success : Width → BitVec 64 | .wide => 1200 | .large => 452

def Guard.clobbers : Width → Guard → List (BitVec 5)
  | .wide, .address => [10, 11, 12] | .wide, .round => []
  | .wide, .align => [11, 12, 13] | .wide, .finish => []
  | .wide, .capacity => [12, 13]
  | .large, .address => [10, 13, 14] | .large, .round => []
  | .large, .align => [14, 15, 16] | .large, .finish => [17]
  | .large, .capacity => [11]

structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [10#5, 11#5, 12#5, 13#5, 14#5, 15#5, 16#5, 17#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Frame.trans {s t u : ArmState} (st : Frame s t) (tu : Frame t u) : Frame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem Frame.sp {s t : ArmState} (frame : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem Frame.aligned {s t : ArmState} (frame : Frame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem Frame.code {s t : ArmState} (frame : Frame s t)
    (base : BitVec 64) (hc : CodeAt s base) : CodeAt t base := by
  intro row hr
  simpa only [frame.program] using hc row hr

theorem block_preserves {α : Sort _} (observe : ArmState → α)
    (base : BitVec 64) (ops : List Op)
    (one : ∀ op ∈ ops, ∀ s, observe (op.effect base s) = observe s)
    (s : ArmState) : observe (block base ops s) = observe s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change observe (block base ops (op.effect base s)) = observe s
    exact (ih (fun p hp => one p (List.mem_cons_of_mem op hp)) _).trans
      (one op (List.mem_cons_self) s)

private theorem guard_one_register (width : Width) (guard : Guard) (op : Op)
    (member : op ∈ guard.ops width) (base : BitVec 64) (reg : BitVec 5)
    (hr : reg ∉ guard.clobbers width) (s : ArmState) :
    r (.GPR reg) (op.effect base s) = r (.GPR reg) s := by
  cases width <;> cases guard <;>
    simp only [Guard.ops, List.mem_cons, List.not_mem_nil, or_false] at member
  case wide.address => rcases member with rfl | rfl | rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case wide.round => rcases member with rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case wide.align => rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case wide.finish => rcases member with rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case wide.capacity => rcases member with rfl | rfl | rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  case large.address => rcases member with rfl | rfl | rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case large.round => rcases member with rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case large.align => rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case large.finish => rcases member with rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, state_simp_rules]
  case large.capacity => rcases member with rfl | rfl | rfl <;>
    simp_all [Guard.clobbers, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_registers (width : Width) (guard : Guard) (s : ArmState)
    (base : BitVec 64) (reg : BitVec 5) (hr : reg ∉ guard.clobbers width) :
    r (.GPR reg) (block base (guard.ops width) s) = r (.GPR reg) s :=
  block_preserves (r (.GPR reg)) base (guard.ops width)
    (fun op member t => guard_one_register width guard op member base reg hr t) s

theorem guard_frame (width : Width) (guard : Guard) (s : ArmState)
    (base : BitVec 64) : Frame s (block base (guard.ops width) s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    apply guard_registers width guard s base reg
    cases width <;> cases guard <;> simp_all [Guard.clobbers]
  · intro reg
    exact block_preserves (r (.SFP reg)) base (guard.ops width)
      (fun op _ t => op.sfp base t reg) s

theorem guard_memory (width : Width) (guard : Guard) (s : ArmState)
    (base : BitVec 64) : (block base (guard.ops width) s).mem = s.mem := by
  apply block_preserves (fun t => t.mem) base (guard.ops width)
  intro op member t
  cases width <;> cases guard <;>
    simp only [Guard.ops, List.mem_cons, List.not_mem_nil, or_false] at member
  case wide.address => rcases member with rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case wide.round => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case wide.align => rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case wide.finish => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case wide.capacity => rcases member with rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  case large.address => rcases member with rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case large.round => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case large.align => rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case large.finish => rcases member with rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]
  case large.capacity => rcases member with rfl | rfl | rfl <;>
    simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_run (width : Width) (guard : Guard) (s : ArmState)
    (base : BitVec 64) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + guard.entry width) :
    run (guard.ops width).length s = block base (guard.ops width) s := by
  apply block_run base (guard.ops width) s hc he ha
  have hpc : r .PC s = base + guard.entry width := hp
  cases width <;> cases guard <;>
    simp (config := {decide := true, instances := true})
      [Guard.ops, Guard.entry, Follows, Op.row, Op.effect, put, next,
       Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

structure Checkpoint (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : Frame s t
  memory : t.mem = s.mem

theorem Checkpoint.refl (s : ArmState) : Checkpoint s s :=
  ⟨⟨0, rfl⟩, Frame.refl s, rfl⟩

theorem Checkpoint.step {s t : ArmState} (reached : Checkpoint s t)
    (width : Width) (guard : Guard) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + guard.entry width) :
    Checkpoint s (block base (guard.ops width) t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := guard_run width guard t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨⟨fuel + (guard.ops width).length, ?_⟩,
    reached.frame.trans (guard_frame width guard t base),
    (guard_memory width guard t base).trans reached.memory⟩
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

theorem address_exit (width : Width) (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 4#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s
    let t := block base (Guard.address.ops width) s
    r (.GPR 10#5) t = pointer ∧ r (.GPR width.usedReg) t = used ∧
      r (.GPR width.addressReg) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 1264#64
        else base + Guard.round.entry width := by
  cases width <;> simp [block, Guard.ops, Guard.entry, Width.usedReg, Width.addressReg,
    Op.effect, put, next, state_simp_rules, Udivti3.adc_carry, Udivti3.radix]

theorem round_exit (width : Width) (s : ArmState) (base : BitVec 64) :
    read_pc (block base (Guard.round.ops width) s) =
      if 2^64 < (r (.GPR width.addressReg) s).toNat + 8 then base + 1264#64
        else base + Guard.align.entry width := by
  cases width <;> simp [block, Guard.ops, Guard.entry, Width.addressReg,
    Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem align_exit (width : Width) (s : ArmState) (base : BitVec 64) :
    let aligned := (r (.GPR width.addressReg) s + 7#64) &&& 18446744073709551608#64
    let padding := aligned - r (.GPR width.addressReg) s
    let t := block base (Guard.align.ops width) s
    r (.GPR width.alignedReg) t = aligned ∧
      r (.GPR width.startReg) t = padding + r (.GPR width.usedReg) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR width.usedReg) s).toNat
        then base + 1264#64 else base + Guard.finish.entry width := by
  cases width <;> simp [block, Guard.ops, Guard.entry, Width.addressReg, Width.alignedReg,
    Width.startReg, Width.usedReg, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem finish_exit (width : Width) (s : ArmState) (base : BitVec 64) :
    let t := block base (Guard.finish.ops width) s
    width.endValue t = r (.GPR width.startReg) s + width.bytes s ∧
      read_pc t = if 2^64 ≤ (r (.GPR width.startReg) s).toNat + (width.bytes s).toNat
        then base + 1264#64 else base + Guard.capacity.entry width := by
  cases width
  · have same : (2^64 < (r (.GPR 11#5) s).toNat + 17) ↔
        (2^64 ≤ (r (.GPR 11#5) s).toNat + 16) := by omega
    simp [block, Guard.ops, Guard.entry, Width.endValue, Width.startReg, Width.bytes,
      Op.effect, put, next, state_simp_rules, cmn_hi_zero, same]
  · simp [block, Guard.ops, Guard.entry, Width.endValue, Width.startReg, Width.bytes,
      Op.effect, put, next, state_simp_rules, Udivti3.adc_carry, Udivti3.radix]

theorem capacity_exit (width : Width) (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
    let t := block base (Guard.capacity.ops width) s
    r (.GPR width.finishReg) t = width.endValue s ∧
      read_pc t = if capacity.toNat < (width.endValue s).toNat
        then base + 1264#64 else base + width.success := by
  cases width <;> simp [block, Guard.ops, Width.finishReg, Width.endValue, Width.success,
    Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, Udivti3.cmp_high]

theorem guard_bytes (width : Width) (guard : Guard) (s : ArmState)
    (base : BitVec 64) (beforeCapacity : guard ≠ .capacity) :
    width.bytes (block base (guard.ops width) s) = width.bytes s := by
  cases width
  · rfl
  · apply guard_registers .large guard s base 11#5
    cases guard <;> simp_all [Guard.clobbers]

end SszArm.NatMulWord.Reserve
