import SszArm.CodecMeasureSingletonOps
import SszArm.DelimitedArena

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open SszArm.Udivti3 (next put flagged branch)

instance (field : StateField) : Decidable (Preserved field) := by
  cases field <;> dsimp [Preserved] <;> infer_instance

inductive Guard where
  | address | round | align | finish | capacity
  deriving DecidableEq

def Guard.ops : Guard → List Op
  | .address => [.loadBase, .loadUsed, .saveResult, .addAddress, .addressGuard]
  | .round => [.compareAlignment, .alignmentGuard]
  | .align => [.addPadding, .maskPadding, .subtractAddress, .addUsed, .usedGuard]
  | .finish => [.compareSize, .sizeGuard]
  | .capacity => [.loadCapacity, .addSize, .compareCapacity, .capacityGuard]

def Guard.pc : Guard → Nat
  | .address => 12 | .round => 32 | .align => 40 | .finish => 60 | .capacity => 68

theorem guard_follows (guard : Guard) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.pc) :
    Follows base guard.ops s := by
  cases guard <;>
    simp_all [Guard.ops, Guard.pc, Follows, Op.pc, effect, next, put, flagged,
      Udivti3.compare, state_simp_rules, BitVec.add_assoc]

theorem guard_runs (guard : Guard) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.pc) :
    run guard.ops.length s = block guard.ops s :=
  block_run _ s base code error (guard_follows guard s base pc)

theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (effect_program op s)

theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (effect_error op s)

theorem block_field (ops : List Op) (s : ArmState) (field : StateField)
    (preserved : Preserved field) : r field (block ops s) = r field s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (effect_field op s field preserved)

theorem block_memory (ops : List Op) (s : ArmState) (notCommit : Op.commit ∉ ops) :
    (block ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    have notOp : op ≠ .commit := by
      intro eq
      apply notCommit
      simp [eq]
    have notRest : Op.commit ∉ rest := by
      intro member
      exact notCommit (List.mem_cons_of_mem _ member)
    exact (ih _ notRest).trans (effect_memory op s notOp)

structure Checkpoint (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  program : t.program = s.program
  error : read_err t = read_err s
  memory : t.mem = s.mem
  fields : ∀ field, Preserved field → r field t = r field s

theorem Checkpoint.refl (s : ArmState) : Checkpoint s s :=
  ⟨⟨0, rfl⟩, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Checkpoint.step {s t : ArmState} (reached : Checkpoint s t)
    (guard : Guard) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None)
    (pc : read_pc t = base + BitVec.ofNat 64 guard.pc) :
    Checkpoint s (block guard.ops t) := by
  have codeT : CodeAt t base := by
    intro op
    rw [reached.program]
    exact code op
  have runT := guard_runs guard t base codeT (reached.error.trans error) pc
  obtain ⟨fuel, runs⟩ := reached.runs
  refine ⟨⟨fuel + guard.ops.length, ?_⟩,
    (block_program _ t).trans reached.program,
    (block_error _ t).trans reached.error,
    (block_memory _ t ?_).trans reached.memory, ?_⟩
  · rw [run_plus, runs, runT]
  · cases guard <;> decide
  · intro field preserved
    exact (block_field _ t field preserved).trans (reached.fields field preserved)

theorem Checkpoint.header {s t : ArmState} (reached : Checkpoint s t)
    (offset : BitVec 64) :
    read_mem_bytes 8 (r (.GPR 1) t + offset) t =
      read_mem_bytes 8 (r (.GPR 1) s + offset) s := by
  rw [reached.fields (.GPR 1) (by decide)]
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.memory]

private theorem cmn_hi (a b : BitVec 64) :
    ((AddWithCarry a b 0#1).2.c = 1#1 ∧ (AddWithCarry a b 0#1).2.z = 0#1) ↔
      2^64 < a.toNat + b.toNat := by
  have zero : (AddWithCarry a b 0#1).2.z = 0#1 ↔
      (AddWithCarry a b 0#1).2.z ≠ 1#1 := by bv_omega
  rw [zero]
  exact Delimited.cmn_hi a b


theorem address_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 12#64) :
    let address := read_mem_bytes 8 (r (.GPR 1) s) s
    let used := read_mem_bytes 8 (r (.GPR 1) s + 16#64) s
    let t := block Guard.address.ops s
    r (.GPR 8) t = address ∧ r (.GPR 9) t = used ∧
      r (.GPR 10) t = used + address ∧
      read_pc t = if 2^64 ≤ used.toNat + address.toNat then base + 168#64
        else base + 32#64 := by
  change r .PC s = base + 12#64 at pc
  simp [block, Guard.ops, effect, next, put, flagged, branch, pc,
    state_simp_rules, Udivti3.adc_value, Udivti3.adc_carry, Udivti3.radix,
    BitVec.add_assoc, apply_ite]

theorem round_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 32#64) :
    read_pc (block Guard.round.ops s) =
      if 2^64 < (r (.GPR 10) s).toNat + 8 then base + 168#64 else base + 40#64 := by
  change r .PC s = base + 32#64 at pc
  simp [block, Guard.ops, effect, next, branch, pc,
    state_simp_rules, cmn_hi, BitVec.add_assoc, apply_ite]

theorem align_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 40#64) :
    let rounded := (r (.GPR 10) s + 7#64) &&& ~~~7#64
    let padding := rounded - r (.GPR 10) s
    let t := block Guard.align.ops s
    r (.GPR 11) t = rounded ∧ r (.GPR 9) t = padding + r (.GPR 9) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 9) s).toNat
        then base + 168#64 else base + 60#64 := by
  change r .PC s = base + 40#64 at pc
  simp [block, Guard.ops, effect, next, put, flagged, branch, pc,
    state_simp_rules, Udivti3.adc_value, Udivti3.adc_carry, Udivti3.radix,
    BitVec.add_assoc, apply_ite]

theorem finish_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 60#64) :
    read_pc (block Guard.finish.ops s) =
      if 2^64 < (r (.GPR 9) s).toNat + 41 then base + 168#64 else base + 68#64 := by
  change r .PC s = base + 60#64 at pc
  simp [block, Guard.ops, effect, next, branch, pc,
    state_simp_rules, cmn_hi, BitVec.add_assoc, apply_ite]

theorem capacity_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 68#64) :
    let capacity := read_mem_bytes 8 (r (.GPR 1) s + 8#64) s
    let finish := r (.GPR 9) s + 40#64
    let t := block Guard.capacity.ops s
    r (.GPR 11) t = capacity ∧ r (.GPR 10) t = finish ∧
      read_pc t = if capacity.toNat < finish.toNat then base + 168#64
        else base + 84#64 := by
  change r .PC s = base + 68#64 at pc
  simp [block, Guard.ops, effect, next, put, Udivti3.compare, branch, pc,
    state_simp_rules, UintCodec.arena_capacity_guard, BitVec.add_assoc, apply_ite]

theorem guard_base (guard : Guard) (s : ArmState) (notAddress : guard ≠ .address) :
    r (.GPR 8) (block guard.ops s) = r (.GPR 8) s := by
  cases guard <;>
    simp_all [block, Guard.ops, effect, next, put, flagged, Udivti3.compare, branch,
      state_simp_rules]

theorem guard_used (guard : Guard) (s : ArmState)
    (notAddress : guard ≠ .address) (notAlign : guard ≠ .align) :
    r (.GPR 9) (block guard.ops s) = r (.GPR 9) s := by
  cases guard <;>
    simp_all [block, Guard.ops, effect, next, put, flagged, Udivti3.compare, branch,
      state_simp_rules]

theorem round_work (s : ArmState) :
    r (.GPR 10) (block Guard.round.ops s) = r (.GPR 10) s := by
  simp [block, Guard.ops, effect, next, branch, state_simp_rules]

end SszArm.Codec.Measure.Singleton
