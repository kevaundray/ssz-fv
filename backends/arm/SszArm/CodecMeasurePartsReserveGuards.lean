import SszArm.CodecMeasurePartsReserveOps
import SszArm.DelimitedArena

set_option autoImplicit false

namespace SszArm.Codec.Measure.PartsReserve

open SszArm.Udivti3 (next put flagged branch)

instance (field : StateField) : Decidable (Preserved field) := by
  cases field <;> dsimp [Preserved] <;> infer_instance

inductive Guard where
  | address | round | align | finish | capacity
  deriving DecidableEq

def Guard.ops : Guard → List Op
  | .address => [.loadBase, .loadUsed, .addAddress, .addressGuard]
  | .round => [.compareAlignment, .alignmentGuard]
  | .align => [.addPadding, .maskPadding, .subtractAddress, .addUsed, .usedGuard]
  | .finish => [.multiplyFive, .multiplyEight, .addSize, .sizeGuard]
  | .capacity => [.loadCapacity, .compareCapacity, .capacityGuard]

def Guard.pc : Guard → Nat
  | .address => 364 | .round => 380 | .align => 388 | .finish => 408 | .capacity => 424

theorem guard_follows (guard : Guard) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.pc) : Follows base guard.ops s := by
  cases guard <;>
    simp_all [Guard.ops, Guard.pc, Follows, Op.pc, effect, next, put, flagged,
      Udivti3.compare, state_simp_rules, BitVec.add_assoc]

theorem guard_runs (guard : Guard) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.pc) :
    run guard.ops.length s = block guard.ops s :=
  block_run _ s base code error (guard_follows guard s base pc)

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
    (pc : read_pc t = base + BitVec.ofNat 64 guard.pc) : Checkpoint s (block guard.ops t) := by
  have codeT : CodeAt t base := by intro op; rw [reached.program]; exact code op
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

theorem Checkpoint.header {s t : ArmState} (reached : Checkpoint s t) (offset : BitVec 64) :
    read_mem_bytes 8 (r (.GPR 20) t + offset) t =
      read_mem_bytes 8 (r (.GPR 20) s + offset) s := by
  rw [reached.fields (.GPR 20) (by decide)]
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.memory]

private theorem cmn_hi (a b : BitVec 64) :
    ((AddWithCarry a b 0#1).2.c = 1#1 ∧ (AddWithCarry a b 0#1).2.z = 0#1) ↔
      2^64 < a.toNat + b.toNat := by
  have zero : (AddWithCarry a b 0#1).2.z = 0#1 ↔
      (AddWithCarry a b 0#1).2.z ≠ 1#1 := by bv_omega
  rw [zero]
  exact Delimited.cmn_hi a b


/-- The omitted source-level Layout multiplication/isize guards follow from the
physical paired Value slice. This hypothesis is on a machine slice length, not
on any logical descriptor capacity. -/
theorem forty_count (count : BitVec 64) (physical : 40 * count.toNat < 2^63) :
    ((count + (count <<< (2 : Nat))) <<< (3 : Nat)).toNat = 40 * count.toNat := by
  bv_omega

theorem address_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 364#64) :
    let address := read_mem_bytes 8 (r (.GPR 20) s) s
    let used := read_mem_bytes 8 (r (.GPR 20) s + 16#64) s
    let t := block Guard.address.ops s
    r (.GPR 8) t = address ∧ r (.GPR 10) t = used ∧
      r (.GPR 11) t = used + address ∧
      read_pc t = if 2^64 ≤ used.toNat + address.toNat then base + 960#64
        else base + 380#64 := by
  change r .PC s = base + 364#64 at pc
  simp [block, Guard.ops, effect, next, put, flagged, branch, pc,
    state_simp_rules, Udivti3.adc_value, Udivti3.adc_carry, Udivti3.radix,
    BitVec.add_assoc, apply_ite]

theorem round_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 380#64) :
    read_pc (block Guard.round.ops s) =
      if 2^64 < (r (.GPR 11) s).toNat + 8 then base + 960#64 else base + 388#64 := by
  change r .PC s = base + 380#64 at pc
  simp [block, Guard.ops, effect, next, branch, pc,
    state_simp_rules, cmn_hi, BitVec.add_assoc, apply_ite]

theorem align_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 388#64) :
    let rounded := (r (.GPR 11) s + 7#64) &&& ~~~7#64
    let padding := rounded - r (.GPR 11) s
    let t := block Guard.align.ops s
    r (.GPR 9) t = rounded ∧ r (.GPR 10) t = padding + r (.GPR 10) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR 10) s).toNat
        then base + 960#64 else base + 408#64 := by
  change r .PC s = base + 388#64 at pc
  simp [block, Guard.ops, effect, next, put, flagged, branch, pc,
    state_simp_rules, Udivti3.adc_value, Udivti3.adc_carry, Udivti3.radix,
    BitVec.add_assoc, apply_ite]

theorem finish_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 408#64) :
    let bytes := ((r (.GPR 26) s + (r (.GPR 26) s <<< (2 : Nat))) <<< (3 : Nat))
    let t := block Guard.finish.ops s
    r (.GPR 11) t = r (.GPR 10) s + bytes ∧
      read_pc t = if 2^64 ≤ (r (.GPR 10) s).toNat + bytes.toNat
        then base + 960#64 else base + 424#64 := by
  change r .PC s = base + 408#64 at pc
  simp [block, Guard.ops, effect, next, put, flagged, branch, pc,
    state_simp_rules, Udivti3.adc_value, Udivti3.adc_carry, Udivti3.radix,
    BitVec.add_assoc, apply_ite]

theorem capacity_exit (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 424#64) :
    let capacity := read_mem_bytes 8 (r (.GPR 20) s + 8#64) s
    let t := block Guard.capacity.ops s
    r (.GPR 12) t = capacity ∧
      read_pc t = if capacity.toNat < (r (.GPR 11) s).toNat then base + 960#64
        else base + 436#64 := by
  change r .PC s = base + 424#64 at pc
  simp [block, Guard.ops, effect, next, put, Udivti3.compare, branch, pc,
    state_simp_rules, UintCodec.arena_capacity_guard, BitVec.add_assoc, apply_ite]

theorem guard_base (guard : Guard) (s : ArmState) (notAddress : guard ≠ .address) :
    r (.GPR 8) (block guard.ops s) = r (.GPR 8) s := by
  cases guard <;> simp_all [block, Guard.ops, effect, next, put, flagged,
    Udivti3.compare, branch, state_simp_rules]

theorem guard_used (guard : Guard) (s : ArmState)
    (notAddress : guard ≠ .address) (notAlign : guard ≠ .align) :
    r (.GPR 10) (block guard.ops s) = r (.GPR 10) s := by
  cases guard <;> simp_all [block, Guard.ops, effect, next, put, flagged,
    Udivti3.compare, branch, state_simp_rules]

theorem round_work (s : ArmState) :
    r (.GPR 11) (block Guard.round.ops s) = r (.GPR 11) s := by
  simp [block, Guard.ops, effect, next, branch, state_simp_rules]

theorem capacity_work (s : ArmState) :
    r (.GPR 11) (block Guard.capacity.ops s) = r (.GPR 11) s := by
  simp [block, Guard.ops, effect, next, put, Udivti3.compare, branch, state_simp_rules]

end SszArm.Codec.Measure.PartsReserve
