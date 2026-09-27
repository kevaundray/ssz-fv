import SszArm.NatAddExec
import SszArm.DelimitedArenaArithmetic

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Reservation guards only clobber the six caller-saved scratch registers. -/
structure ArenaFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem ArenaFrame.refl (s : ArmState) : ArenaFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem ArenaFrame.trans {s t u : ArmState} (st : ArenaFrame s t)
    (tu : ArenaFrame t u) : ArenaFrame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem ArenaFrame.sp {s t : ArmState} (frame : ArenaFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem ArenaFrame.aligned {s t : ArmState} (frame : ArenaFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem ArenaFrame.code {s t : ArmState} (frame : ArenaFrame s t)
    (base : BitVec 64) (hc : CodeAt s base) : CodeAt t base := by
  intro row hr
  simpa only [frame.program] using hc row hr

inductive ArenaCheckKind where
  | bigAddress | bigRound | bigAlign | bigEnd | bigCapacity | smallAddress | smallRound | smallAlign | smallEnd | smallCapacity
  deriving DecidableEq

def ArenaCheckKind.ops : ArenaCheckKind → List Op
  | .bigAddress => [.p204, .p208, .p212, .p216]
  | .bigRound => [.p220, .p224]
  | .bigAlign => [.p228, .p232, .p236, .p240, .p244]
  | .bigEnd => [.p248, .p252]
  | .bigCapacity => [.p256, .p260, .p264]
  | .smallAddress => [.p1112, .p1116, .p1120, .p1124]
  | .smallRound => [.p1128, .p1132]
  | .smallAlign => [.p1136, .p1140, .p1144, .p1148, .p1152]
  | .smallEnd => [.p1156, .p1160]
  | .smallCapacity => [.p1164, .p1168, .p1172, .p1176]

def ArenaCheckKind.entry : ArenaCheckKind → BitVec 64
  | .bigAddress => 204#64
  | .bigRound => 220#64
  | .bigAlign => 228#64
  | .bigEnd => 248#64
  | .bigCapacity => 256#64
  | .smallAddress => 1112#64
  | .smallRound => 1128#64
  | .smallAlign => 1136#64
  | .smallEnd => 1156#64
  | .smallCapacity => 1164#64

def ArenaCheckKind.clobbers : ArenaCheckKind → List (BitVec 5)
  | .bigAddress => [9#5, 12#5, 13#5]
  | .bigRound => []
  | .bigAlign => [10#5, 12#5, 13#5]
  | .bigEnd => [11#5]
  | .bigCapacity => [13#5]
  | .smallAddress => [8#5, 10#5, 11#5]
  | .smallRound => []
  | .smallAlign => [10#5, 11#5, 12#5]
  | .smallEnd => []
  | .smallCapacity => [11#5, 12#5]

theorem arena_guard_registers (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) (reg : BitVec 5) (hr : reg ∉ kind.clobbers) :
    r (.GPR reg) (block base kind.ops s) = r (.GPR reg) s := by
  cases kind <;> simp only [ArenaCheckKind.clobbers, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hr <;>
    simp (disch := simp_all) [ArenaCheckKind.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem arena_guard_frame (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) : ArenaFrame s (block base kind.ops s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg hr
    apply arena_guard_registers kind s base reg
    cases kind <;> simp_all [ArenaCheckKind.clobbers]
  · intro reg
    cases kind <;> simp [ArenaCheckKind.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem arena_guard_memory (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) : (block base kind.ops s).mem = s.mem := by
  cases kind <;> simp [ArenaCheckKind.ops, block, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem arena_guard_run (kind : ArenaCheckKind) (s : ArmState)
    (base : BitVec 64) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + kind.entry) :
    run kind.ops.length s = block base kind.ops s := by
  apply block_run base kind.ops s hc he ha
  have hpc : r .PC s = base + kind.entry := hp
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [ArenaCheckKind.ops, ArenaCheckKind.entry, Follows, Op.row, Op.effect, put, next,
       Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

/-- Read-only guard prefixes compose actual runs and preserve the arena header. -/
structure ArenaCheckpoint (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : ArenaFrame s t
  memory : t.mem = s.mem

theorem ArenaCheckpoint.refl (s : ArmState) : ArenaCheckpoint s s :=
  ⟨⟨0, rfl⟩, ArenaFrame.refl s, rfl⟩

theorem ArenaCheckpoint.step {s t : ArmState} (reached : ArenaCheckpoint s t)
    (kind : ArenaCheckKind) (base : BitVec 64) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc t = base + kind.entry) :
    ArenaCheckpoint s (block base kind.ops t) := by
  obtain ⟨fuel, hr⟩ := reached.runs
  have hrun := arena_guard_run kind t base (reached.frame.code base hc)
    (reached.frame.error.trans he) (reached.frame.aligned ha) hp
  refine ⟨⟨fuel + kind.ops.length, ?_⟩,
    reached.frame.trans (arena_guard_frame kind t base),
    (arena_guard_memory kind t base).trans reached.memory⟩
  rw [run_plus, hr, hrun]

theorem ArenaCheckpoint.header {s t : ArmState} (reached : ArenaCheckpoint s t)
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

theorem arena_big_address_exit (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 5#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s
    let t := block base ArenaCheckKind.bigAddress.ops s
    r (.GPR 9#5) t = pointer ∧ r (.GPR 12#5) t = used ∧
      r (.GPR 13#5) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 1248#64 else base + 220#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_big_round_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base ArenaCheckKind.bigRound.ops s) =
      if 2^64 < (r (.GPR 13#5) s).toNat + 8 then base + 1248#64 else base + 228#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem arena_big_align_exit (s : ArmState) (base : BitVec 64) :
    let aligned := (r (.GPR 13#5) s + 7#64) &&& 18446744073709551608#64
    let padding := aligned - r (.GPR 13#5) s
    let t := block base ArenaCheckKind.bigAlign.ops s
    r (.GPR 10#5) t = aligned ∧ r (.GPR 13#5) t = padding ∧
      r (.GPR 12#5) t = padding + r (.GPR 12#5) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 12#5) s).toNat
        then base + 1248#64 else base + 248#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_big_end_exit (s : ArmState) (base : BitVec 64) :
    let t := block base ArenaCheckKind.bigEnd.ops s
    r (.GPR 11#5) t = r (.GPR 12#5) s + r (.GPR 11#5) s ∧
      read_pc t = if 2^64 ≤ (r (.GPR 12#5) s).toNat + (r (.GPR 11#5) s).toNat
        then base + 1248#64 else base + 256#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_big_capacity_exit (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s
    let t := block base ArenaCheckKind.bigCapacity.ops s
    r (.GPR 13#5) t = capacity ∧
      read_pc t = if capacity.toNat < (r (.GPR 11#5) s).toNat
        then base + 1248#64 else base + 268#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, Udivti3.cmp_high]

theorem arena_small_address_exit (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 5#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s
    let t := block base ArenaCheckKind.smallAddress.ops s
    r (.GPR 8#5) t = pointer ∧ r (.GPR 10#5) t = used ∧
      r (.GPR 11#5) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 1248#64 else base + 1128#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_small_round_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base ArenaCheckKind.smallRound.ops s) =
      if 2^64 < (r (.GPR 11#5) s).toNat + 8 then base + 1248#64 else base + 1136#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem arena_small_align_exit (s : ArmState) (base : BitVec 64) :
    let aligned := (r (.GPR 11#5) s + 7#64) &&& 18446744073709551608#64
    let padding := aligned - r (.GPR 11#5) s
    let t := block base ArenaCheckKind.smallAlign.ops s
    r (.GPR 12#5) t = aligned ∧ r (.GPR 11#5) t = padding ∧
      r (.GPR 10#5) t = padding + r (.GPR 10#5) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 10#5) s).toNat
        then base + 1248#64 else base + 1156#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules,
    Udivti3.adc_carry, Udivti3.radix]

theorem arena_small_end_exit (s : ArmState) (base : BitVec 64) :
    read_pc (block base ArenaCheckKind.smallEnd.ops s) =
      if 2^64 < (r (.GPR 10#5) s).toNat + 17 then base + 1248#64 else base + 1164#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, state_simp_rules, cmn_hi_zero]

theorem arena_small_capacity_exit (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s
    let finish := r (.GPR 10#5) s + 16#64
    let t := block base ArenaCheckKind.smallCapacity.ops s
    r (.GPR 12#5) t = capacity ∧ r (.GPR 11#5) t = finish ∧
      read_pc t = if capacity.toNat < finish.toNat then base + 1248#64 else base + 1180#64 := by
  simp [block, ArenaCheckKind.ops, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, Udivti3.cmp_high]

end SszArm.NatAdd
