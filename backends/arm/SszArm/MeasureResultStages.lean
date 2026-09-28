import SszArm.MeasureResultLower

namespace SszArm.Measure.Result

@[irreducible] def spillStage (kind : Lower) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 12))
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (savedPair s kind.tmp))

@[irreducible] def payloadStage (kind : Lower) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.finish - 12))
    (w (.GPR kind.tmp) 0#64 (w (.GPR 9#5) (r (.GPR 19#5) s + kind.offset)
      (kind.kind.store s (r (.GPR 19#5) s + kind.offset) (kind.low s) (kind.high s))))

@[irreducible] def reloadStage (kind : Lower) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 kind.finish)
    (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s)
        (w (.GPR kind.tmp) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)))

@[simp] theorem spillStage_pc (kind : Lower) (s : ArmState) (base : BitVec 64) :
    read_pc (spillStage kind s base) = base + BitVec.ofNat 64 (kind.start + 12) := by
  simp [spillStage, state_simp_rules]

@[simp] theorem payloadStage_pc (kind : Lower) (s : ArmState) (base : BitVec 64) :
    read_pc (payloadStage kind s base) = base + BitVec.ofNat 64 (kind.finish - 12) := by
  simp [payloadStage, state_simp_rules]

theorem spillStage_aligned (kind : Lower) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (spillStage kind s base) := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simpa [spillStage, savedPair, CheckSPAlignment, state_simp_rules] using lower

theorem payloadStage_aligned (kind : Lower) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (payloadStage kind s base) := by
  cases kind <;> simpa (config := {decide := true})
    [payloadStage, Lower.tmp, Lower.kind, Payload.store, CheckSPAlignment, state_simp_rules] using aligned

private theorem scratch_restore (s : ArmState) (tmp : BitVec 5)
    (low high pointer stack : BitVec 64) (nine : tmp ≠ 9#5) (sp : tmp ≠ 31#5) :
    w (.GPR 31#5) (r (.GPR 31#5) s)
      (w (.GPR 9#5) low (w (.GPR tmp) high
        (w (.GPR 9#5) pointer (w (.GPR 31#5) stack s)))) =
      w (.GPR 9#5) low (w (.GPR tmp) high s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases isNine : reg = 9#5 <;> by_cases isTmp : reg = tmp <;>
        by_cases isSP : reg = 31#5 <;> (try subst reg) <;>
        simp_all [NatExact.r_gpr_w, state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro bytes address; simp [state_simp_rules]

theorem stages_assemble (kind : Lower) (s : ArmState) (base : BitVec 64) :
    reloadStage kind (payloadStage kind (spillStage kind s base) base) base = kind.result s base := by
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have restored := scratch_restore (kind.memory s) kind.tmp
    (read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (kind.memory s))
    (read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (kind.memory s))
    (r (.GPR 19#5) s + kind.offset) (r (.GPR 31#5) s - 16#64)
    (by cases kind <;> decide) (by cases kind <;> decide)
  have bridge := congrArg (w .PC (base + BitVec.ofNat 64 kind.finish)) restored
  cases kind <;>
    simpa (config := {decide := true})
      [reloadStage, payloadStage, spillStage, Lower.result, Lower.memory,
       Lower.start, Lower.finish, Lower.tmp, Lower.kind, Lower.offset, Lower.low, Lower.high,
       Payload.store, savedPair, state_simp_rules, NatExact.store_w, NatExact.gpr_w_pc,
       BitVec.sub_add_cancel, address] using bridge

end SszArm.Measure.Result
