import SszArm.DelimitedPrepared

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private def smallReadyOps (limit : Option Nat) : List Op :=
  smallOps ++ if limit.isSome then [] else noLimitOps

private theorem small_ready_register (s : ArmState) (base : BitVec 64)
    (limit : Option Nat) (reg : BitVec 5) (preserved : reg ∉ [8#5, 19#5, 20#5]) :
    r (.GPR reg) (block base (smallReadyOps limit) s) = r (.GPR reg) s := by
  cases limit <;>
    simp (disch := simp_all) [smallReadyOps, smallOps, noLimitOps, block, Op.effect,
      put, next, state_simp_rules]

private theorem small_ready_memory (s : ArmState) (base : BitVec 64) (limit : Option Nat) :
    (block base (smallReadyOps limit) s).mem = s.mem := by
  cases limit <;> simp [smallReadyOps, smallOps, noLimitOps, block, Op.effect,
    put, next, state_simp_rules]

private theorem small_ready_vector (s : ArmState) (base : BitVec 64)
    (limit : Option Nat) (reg : BitVec 5) :
    r (.SFP reg) (block base (smallReadyOps limit) s) = r (.SFP reg) s := by
  cases limit <;> simp [smallReadyOps, smallOps, noLimitOps, block, Op.effect,
    put, next, state_simp_rules]

private theorem small_ready_fields (s : ArmState) (base : BitVec 64) (limit : Option Nat)
    (tag : read_mem_bytes 4 (r (.GPR 1#5) s) s = if limit.isSome then 1#32 else 0#32) :
    let t := block base (smallReadyOps limit) s
    r (.GPR 20#5) t = 0#64 ∧ r (.GPR 19#5) t = r (.GPR 24#5) s ∧
      read_pc t = if limit.isSome then base + 364#64 else base + 540#64 := by
  have fields := small_fields s base
  cases limit with
  | none =>
    simpa [smallReadyOps, noLimitOps, block, Op.effect, put, next, state_simp_rules] using
      And.intro fields.1 fields.2.1
  | some cap =>
    simpa [smallReadyOps, tag] using And.intro fields.1 (And.intro fields.2.1 fields.2.2.2.2)

private theorem small_ready_run (s : ArmState) (base : BitVec 64) (limit : Option Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 148#64)
    (tag : read_mem_bytes 4 (r (.GPR 1#5) s) s = if limit.isSome then 1#32 else 0#32) :
    run (if limit.isSome then 5 else 6) s = block base (smallReadyOps limit) s := by
  have first := small_run s base hc he ha hp
  cases limit with
  | some cap => simpa [smallReadyOps] using first
  | none =>
    let a := block base smallOps s
    have codeA : CodeAt a base := by
      simpa only [a, CodeAt, block_program] using hc
    have pcA : read_pc a = base + 168#64 := by
      simpa only [tag, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        BitVec.reduceEq] using (small_fields s base).2.2.2.2
    have second := noLimit_run a base codeA ((block_error base smallOps s).trans he)
      (block_aligned base smallOps s ha) pcA
    change run (5 + 1) s = _
    rw [run_plus, first, second]
    rfl

/-- The native small representation needs no scratch, and the absent-option
path executes its real p168 branch before reaching representation validation. -/
theorem small_prepare (s u : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (owned : Owned s limit data) (counted : Counted s u base limit data)
    (hc : CodeAt s base) (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (small : (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high = 0#64) :
    ∃ ready t, run (if limit.isSome then 5 else 6) u = t ∧ Ready s t base limit data ready ∧
      r (.GPR 1#5) t = r (.GPR 1#5) s ∧
      read_pc t = if limit.isSome then base + 364#64 else base + 540#64 := by
  let count := SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)
  let ready : SszNative.Delimited.Prepared := ⟨count, (arenaOf s).used, none⟩
  let t := block base (smallReadyOps limit) u
  have countSmall : count.high = 0#64 := small
  have prepared : SszNative.Delimited.prepare (arenaOf s) count = some ready := by
    simp only [SszNative.Delimited.prepare, countSmall, ↓reduceIte]
    rfl
  have allocation := prepared_allocation limit data (arenaOf s) ready owned.physical
    nonempty delimiter prepared
  have tag : read_mem_bytes 4 (r (.GPR 1#5) u) u = if limit.isSome then 1#32 else 0#32 := by
    rw [counted.arguments 1#5 (by simp)]
    exact option_tag u (r (.GPR 1#5) s) limit counted.inputs.option
  have codeU : CodeAt u base := by simpa only [CodeAt, counted.program] using hc
  have pcU : read_pc u = base + 148#64 := by simpa only [small, ↓reduceIte] using counted.pc
  have executed := small_ready_run u base limit codeU counted.error counted.aligned pcU tag
  have fields := small_ready_fields u base limit tag
  have memory : t.mem = u.mem := small_ready_memory u base limit
  have sp : r (.GPR 31#5) t = r (.GPR 31#5) u :=
    small_ready_register u base limit 31#5 (by decide)
  have frame : MemoryFrame (localWrites s) s t := by
    intro address outside
    exact (congrFun memory address).trans (counted.frame address outside)
  have cursor := counted.frame.load ((r (.GPR 4#5) s).toNat + 16) 8
    (by have bound := owned.arenaBound; omega) (owned.arenaLocal.subspan 16 8 (by decide))
  have optionAddress : r (.GPR 1#5) t = r (.GPR 1#5) s :=
    (small_ready_register u base limit 1#5 (by decide)).trans
      (counted.arguments 1#5 (by simp))
  refine ⟨ready, t, executed, ?_, optionAddress, fields.2.2⟩
  refine ⟨prepared, allocation, (block_program base (smallReadyOps limit) u).trans counted.program,
    (block_error base (smallReadyOps limit) u).trans counted.error,
    block_aligned base (smallReadyOps limit) u counted.aligned,
    counted.saved.of_memory memory sp (fun reg _ _ =>
      congrArg (BitVec.setWidth 64) (small_ready_vector u base limit reg)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, small, ?_, frame⟩
  · intro reg member
    have preserved : reg ∉ [8#5, 19#5, 20#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    rw [small_ready_register u base limit reg preserved]
    apply counted.arguments reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl | rfl <;> simp
  · rw [small_ready_register u base limit 25#5 (by decide)]
    exact counted.preceding
  · rw [small_ready_register u base limit 26#5 (by decide)]
    exact counted.counter
  · rw [small_ready_register u base limit 24#5 (by decide)]
    exact counted.low
  · rw [small_ready_register u base limit 23#5 (by decide)]
    exact counted.high
  · exact fields.1
  · rw [fields.2.1, counted.low]
    simp [ready, count, SszNative.Delimited.Prepared.payload, BitVec.ofNat_toNat]
  · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) 8]
    simpa only [ready, arenaOf, widthLoad, BitVec.ofNat_add,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using Option.some.inj cursor

end SszArm.Delimited
