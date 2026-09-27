import SszArm.UintFailure

namespace SszArm.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

@[simp] theorem success_ready_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (successReady s base) = r (.GPR 31#5) s := by
  tail_expand
  try simp [BitVec.sub_add_cancel]

@[simp] theorem scope_ready_sp (s : ArmState) :
    r (.GPR 31#5) (scopeReady s) = r (.GPR 31#5) s := by
  tail_expand
  try simp [BitVec.sub_add_cancel]

@[simp] theorem failure_ready_sp (s : ArmState) :
    r (.GPR 31#5) (failureReady s) = r (.GPR 31#5) s := by
  failure_return_expand
  rw [Memcpy.result_frame _ (.GPR 31#5) (by simp [Memcpy.Preserved])]
  exact (failure_prepared_registers s).2.2.2.2.2.1

@[simp] theorem returned_load (s : ArmState) : widthLoad (returned s) = widthLoad s := by
  funext a n
  simp [widthLoad, returned, state_simp_rules]

/-- The complete success tail: STP of the Nat, the UInt value byte, the shared
result-tag stores, six LDPs, ADD SP, and RET. -/
theorem success_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4460#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 22 s = returned (successReady s base) := by
  rw [show 22 = 4 + 18 by decide, run_plus, success_block s base hc hp he ha]
  apply tag_tail _ base
  · apply bool_codeAt
    simpa only [CodeAt, block_program] using hc
  · have hpc : r .PC s = base + 4460#64 := hp
    simp [successOps, block, Op.effect, next, StoreOp.effect,
      state_simp_rules, hpc, BitVec.add_assoc]
  · simpa only [block_error] using he
  · exact block_aligned _ s ha

/-- Scope copies both original descriptor words. In particular it does not
canonicalize an empty or high-zero Large descriptor to Small. -/
theorem scope_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4544#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 55 s = returned (scopeReady s) := by
  let t := block (scopeOps.map Prod.snd) s
  have htc : BoolCodec.CodeAt t base := bool_codeAt (by
    simpa only [t, CodeAt, block_program] using hc)
  have hte : read_err t = .None := by simpa only [t, block_error] using he
  have hta : CheckSPAlignment t := block_aligned _ s ha
  have htp : read_pc t = base + 4720#64 := by
    have hpc : r .PC s = base + 4544#64 := hp
    simp [t, scopeOps, block, Op.effect, next, put, StoreOp.effect,
      state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 55 = 44 + (3 + 8) by decide, run_plus, scope_block s base hc hp he ha]
  change run (3 + 8) t = _
  rw [run_plus, error_tail t base htc htp hte]
  apply epilogue _ base
  · simpa [BoolCodec.CodeAt, tagsStored, reasonStored, tagInitialized, state_simp_rules] using htc
  · have hpc : r .PC t = base + 4720#64 := htp
    simp [tagsStored, reasonStored, tagInitialized, state_simp_rules, hpc, BitVec.add_assoc]
  · simpa [tagsStored, reasonStored, tagInitialized, state_simp_rules] using hte
  · simpa [tagsStored, reasonStored, tagInitialized, state_simp_rules] using hta

/-- Scratch exhaustion executes the real BL to the linked memcpy at 104240,
returns to 4912, writes reason 32768, then restores the original saved LR by LDP.
The numeric resource-reservation failure is a separate caller-side premise. -/
theorem failure_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4816#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 56 s = returned (failureReady s) := by
  let t := failurePrepared s
  have hr := failure_prepared_registers s
  have htc : CodeAt t base := by simpa only [t, failurePrepared, CodeAt, block_program] using hc
  have hte : read_err t = .None := by simpa only [t, failurePrepared, block_error] using he
  have hta : CheckSPAlignment t := block_aligned _ s ha
  have htp : read_pc t = base + 104240#64 := by
    rw [show read_pc t = read_pc s + 99424#64 from hr.2.2.2.2.2.2.2, hp]
    simp [BitVec.add_assoc]
  have hcopy : run 20 t = Memcpy.result t := by
    have h := Memcpy.program_run t (base + 104240#64) (memcpy_codeAt htc) htp hte
    simpa only [show r (.GPR 2) t = 48#64 from hr.2.2.1,
      BitVec.toNat_ofNat, Memcpy.fuel] using h
  have huc : CodeAt (Memcpy.result t) base := by
    simpa only [CodeAt, Memcpy.result_program] using htc
  have hue : read_err (Memcpy.result t) = .None :=
    (Memcpy.result_frame t .ERR trivial).trans hte
  have hua : CheckSPAlignment (Memcpy.result t) := by
    simpa only [CheckSPAlignment, state_simp_rules,
      Memcpy.result_frame t (.GPR 31#5) (by simp [Memcpy.Preserved])] using hta
  have hup : read_pc (Memcpy.result t) = base + 4912#64 := by
    rw [Memcpy.result_return]
    change r (.GPR 30#5) (failurePrepared s) = _
    rw [hr.2.2.2.2.2.2.1, hp]
    simp [BitVec.add_assoc]
  have hvc : BoolCodec.CodeAt (failureReady s) base := by
    apply bool_codeAt
    simpa only [failureReady, CodeAt, block_program, t] using huc
  have hve : read_err (failureReady s) = .None := by
    simpa only [failureReady, block_error, t] using hue
  have hva : CheckSPAlignment (failureReady s) := block_aligned _ _ hua
  have hvp : read_pc (failureReady s) = base + 4732#64 := by
    have hpc : r .PC (Memcpy.result t) = base + 4912#64 := hup
    change read_pc (block (failureReturnOps.map Prod.snd) (Memcpy.result t)) = _
    simp [failureReturnOps, block, Op.effect, next, put, state_simp_rules,
      hpc, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [show 56 = 24 + (20 + (4 + 8)) by decide, run_plus,
    failure_block s base hc hp he ha]
  change run (20 + (4 + 8)) t = _
  rw [run_plus, hcopy, run_plus,
    failure_return_block (Memcpy.result t) base huc hup hue hua]
  exact epilogue (failureReady s) base hvc hvp hve hva

/-- Absolute success result, complete finite execution, original return address,
all twelve saved registers, caller SP, and byte-level frame. -/
theorem success_correct (s : ArmState) (base : BitVec 64) (value : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 4460#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hs : Separated s)
    (hn : NatPair s (r (.GPR 12#5) s) (r (.GPR 10#5) s) value) :
    Returned s (run 22 s) ∧ read_err (run 22 s) = .None ∧
    SszNative.UintCodec.ResultAt (widthLoad (run 22 s))
      (r (.GPR 0#5) s).toNat (.ok (.uint value)) := by
  rw [success_run s base hc hp he ha]
  refine ⟨returned_contract s _ hs (success_ready_sp s base) (success_ready_frame s base hs), ?_, ?_⟩
  · have hb : read_err (successReady s base) = .None :=
      (afterJump_error tagStores (block (successOps.map Prod.snd) s) base 4732).trans
        ((block_error _ s).trans he)
    simpa [returned, state_simp_rules] using hb
  · rw [returned_load]
    exact success_ready_result s base value hs hn

/-- Absolute Scope result. Expected is a mathematical Nat, while actual is the
unsigned Small input length copied directly from x3. -/
theorem scope_correct (s : ArmState) (base : BitVec 64) (expected : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 4544#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hs : Separated s)
    (hn : NatPair s (r (.GPR 8#5) s) (r (.GPR 9#5) s) expected) :
    Returned s (run 55 s) ∧ read_err (run 55 s) = .None ∧
    SszNative.UintCodec.ResultAt (widthLoad (run 55 s))
      (r (.GPR 0#5) s).toNat (.error (.scope expected (r (.GPR 3#5) s).toNat)) := by
  rw [scope_run s base hc hp he ha]
  refine ⟨returned_contract s _ hs (scope_ready_sp s) (scope_ready_frame s hs), ?_, ?_⟩
  · have hb : read_err (block (scopeOps.map Prod.snd) s) = .None :=
      (block_error _ s).trans he
    simpa [returned, scopeReady, tagsStored, reasonStored, tagInitialized,
      state_simp_rules] using hb
  · rw [returned_load]
    exact scope_ready_result s expected hs hn

/-- Absolute ScratchExhausted image, established by actual output stores and the
linked 48-byte memcpy. No output field or source-zero fact is a precondition. -/
theorem scratch_exhausted_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 4816#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hs : Separated s) :
    Returned s (run 56 s) ∧ read_err (run 56 s) = .None ∧
    SszNative.UintCodec.scratchExhaustedAt (widthLoad (run 56 s)) (r (.GPR 0#5) s).toNat := by
  rw [failure_run s base hc hp he ha]
  refine ⟨returned_contract s _ hs (failure_ready_sp s) (failure_ready_frame s hs), ?_, ?_⟩
  · have hm : read_err (Memcpy.result (failurePrepared s)) = .None :=
      (Memcpy.result_frame (failurePrepared s) .ERR trivial).trans
        ((block_error _ s).trans he)
    have hb := (block_error (failureReturnOps.map Prod.snd)
      (Memcpy.result (failurePrepared s))).trans hm
    simpa [returned, failureReady, state_simp_rules] using hb
  · rw [returned_load]
    exact failure_ready_result s hs

end SszArm.UintCodec.Tail
