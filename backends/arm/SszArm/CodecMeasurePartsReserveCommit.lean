import SszArm.CodecMeasurePartsReserveChecks

set_option autoImplicit false

namespace SszArm.Codec.Measure.PartsReserve

open Delimited (MemoryFrame)

def commitOps : List Op := [.zeroIndex, .addPointer, .resultPointer, .firstSlot, .commit]

theorem commit_runs (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 436#64) : run 5 s = block commitOps s := by
  apply block_run commitOps s base code error
  change r .PC s = base + 436#64 at pc
  simp [commitOps, Follows, Op.pc, effect, Udivti3.put, Udivti3.next,
    state_simp_rules, pc, BitVec.add_assoc]

theorem commit_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 436#64) :
    let t := block commitOps s
    read_pc t = base + 456#64 ∧ r (.GPR 23) t = 0#64 ∧
      r (.GPR 24) t = r (.GPR 8) s + r (.GPR 10) s ∧
      r (.GPR 25) t = r (.GPR 31) s + 208#64 ∧
      r (.GPR 29) t = r (.GPR 9) s + 16#64 ∧
      t.mem = (write_mem_bytes 8 (r (.GPR 20) s + 16#64) (r (.GPR 11) s) s).mem := by
  change r .PC s = base + 436#64 at pc
  simp [block, commitOps, effect, Udivti3.put, Udivti3.next,
    state_simp_rules, pc, BitVec.add_assoc]

theorem commit_frame (s : ArmState)
    (header : (r (.GPR 20) s).toNat + 24 ≤ 2^64) :
    MemoryFrame [((r (.GPR 20) s).toNat + 16, 8)] s (block commitOps s) := by
  have address : (r (.GPR 20) s + 16#64).toNat = (r (.GPR 20) s).toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have stored := Delimited.store_frame s (r (.GPR 20) s + 16#64) 8 (r (.GPR 11) s)
    (by rw [address]; omega)
  intro a outside
  have memory : (block commitOps s).mem =
      (write_mem_bytes 8 (r (.GPR 20) s + 16#64) (r (.GPR 11) s) s).mem := by
    simp [block, commitOps, effect, Udivti3.put, Udivti3.next, state_simp_rules]
  rw [memory]
  exact stored a (by simpa only [address] using outside)

theorem commit_cursor (s : ArmState)
    (header : (r (.GPR 20) s).toNat + 24 ≤ 2^64) :
    read_mem_bytes 8 (r (.GPR 20) s + 16#64) (block commitOps s) = r (.GPR 11) s := by
  have memory : (block commitOps s).mem =
      (write_mem_bytes 8 (r (.GPR 20) s + 16#64) (r (.GPR 11) s) s).mem := by
    simp [block, commitOps, effect, Udivti3.put, Udivti3.next, state_simp_rules]
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp memory]
  apply BoolCodec.read_mem_bytes_write_mem_bytes_same
  have address : (r (.GPR 20) s + 16#64).toNat = (r (.GPR 20) s).toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [address]
  omega

structure Committed (s t : ArmState) (base : BitVec 64)
    (allocation : SszNative.Arena.Reservation) : Prop where
  pc : read_pc t = base + 456#64
  program : t.program = s.program
  error : read_err t = read_err s
  index : r (.GPR 23) t = 0#64
  pointer : (r (.GPR 24) t).toNat = allocation.pointer
  cursor : (read_mem_bytes 8 (r (.GPR 20) s + 16#64) t).toNat = allocation.used
  frame : MemoryFrame [((r (.GPR 20) s).toNat + 16, 8)] s t
  fields : ∀ field, Preserved field → r field t = r field s

/-- The positive retained reservation commits before the first measure_child
call at +472. A failing native check performs no arena or Plan slot write. -/
theorem reserve_runs (s : ArmState) (base address capacity used count : BitVec 64)
    (code : Linked.MeasureParts.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 364#64)
    (header : (r (.GPR 20) s).toNat + 24 ≤ 2^64)
    (positive : 0 < count.toNat) (physical : 40 * count.toNat < 2^63)
    (countRegister : r (.GPR 26) s = count)
    (headerBase : read_mem_bytes 8 (r (.GPR 20) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 20) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 20) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧
      ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat (5 * count.toNat) = none ∧
          Checkpoint s t ∧ read_pc t = base + 960#64) ∨
        ∃ allocation, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
          (5 * count.toNat) = some allocation ∧ Committed s t base allocation) := by
  obtain ⟨fuel, u, runs, reached, failed | success⟩ :=
    checks_runs s base address capacity used count (code_of_linked s base code) error pc
      positive physical countRegister headerBase headerCapacity headerUsed
  · exact ⟨fuel, u, runs, Or.inl ⟨failed.1, reached, failed.2⟩⟩
  · rcases success with ⟨checks, upc, ub, us, uf, rounded⟩
    let allocation : SszNative.Arena.Reservation :=
      ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
        SszNative.Arena.finish address.toNat used.toNat (5 * count.toNat)⟩
    have allocated : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
        (5 * count.toNat) = some allocation :=
      (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) allocation).2 ⟨checks, rfl⟩
    have codeU : CodeAt u base := by
      intro op
      rw [reached.program]
      exact code_of_linked s base code op
    have headerU : (r (.GPR 20) u).toNat + 24 ≤ 2^64 := by
      rw [reached.fields (.GPR 20) (by decide)]
      exact header
    have commitRun := commit_runs u base codeU (reached.error.trans error) upc
    have committed := commit_summary u base upc
    refine ⟨fuel + 5, block commitOps u, ?_, Or.inr ⟨allocation, allocated, ?_⟩⟩
    · rw [run_plus, runs, commitRun]
    · refine ⟨committed.1, (block_program _ u).trans reached.program,
        (block_error _ u).trans reached.error, committed.2.1, ?_, ?_, ?_, ?_⟩
      · rw [committed.2.2.1, ub, BitVec.toNat_add, us]
        apply Nat.mod_eq_of_lt
        have geometry := SszNative.Arena.start_pointer address.toNat used.toNat
        have bound := (SszNative.Arena.aligned_bounds (address.toNat + used.toNat)).2
        have rounding := checks.2.2.1
        omega
      · have cursor := commit_cursor u headerU
        rw [reached.fields (.GPR 20) (by decide)] at cursor
        exact (congrArg BitVec.toNat cursor).trans uf
      · intro a outside
        have outsideU : ∀ span ∈ [((r (.GPR 20) u).toNat + 16, 8)],
            a.toNat < span.1 ∨ span.1 + span.2 ≤ a.toNat := by
          rw [reached.fields (.GPR 20) (by decide)]
          exact outside
        exact (commit_frame u headerU a outsideU).trans (congrFun reached.memory a)
      · intro field preserved
        exact (block_field _ u field preserved).trans (reached.fields field preserved)

end SszArm.Codec.Measure.PartsReserve
