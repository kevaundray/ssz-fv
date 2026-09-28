import SszArm.EmitUintWidthExec
import SszArm.EmitUintOwned

namespace SszArm.Emit.Uint

def scanPureOps : List WidthOp :=
  [.p60, .p64, .p72, .p76, .p80, .p84, .p120, .p124, .p128, .p132, .p136, .p140, .p896]

theorem scan_pure_frame (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (hops : ∀ op ∈ ops, op ∈ scanPureOps) : NatNarrow.Frame s (widthBlock base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := hops op List.mem_cons_self
    have hf : NatNarrow.Frame s (op.effect base s) := by
      cases op <;> simp_all only [scanPureOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact WidthOp.program _ _ _
        · exact WidthOp.error _ _ _
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [WidthOp.effect, put, next, Dispatch.next,
            Dispatch.compare64, Dispatch.compare32, state_simp_rules]
        · intro reg; exact WidthOp.vector _ _ _ _
        · intro a ha
          simp [WidthOp.effect, put, next, Dispatch.next,
            Dispatch.compare64, Dispatch.compare32, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hops op (List.mem_cons_of_mem _ hop)))

theorem scan_frame_code {s t : ArmState} (frame : NatNarrow.Frame s t) {base : BitVec 64}
    (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, frame.program] using code

def scanLoadOps : List WidthOp := [.p88, .p92, .p96, .p100, .p104, .p108, .p112, .p116]

def scanLoadResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + 120#64) (w (.GPR 11#5) limb (NatCompare.saved s 9#5))

theorem scan_load_run (s : ArmState) (base limb : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 88#64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hread : read_mem_bytes 8 (r (.GPR 8#5) s + (r (.GPR 10#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb) :
    run 8 s = scanLoadResult s base limb := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + 88#64 := hp
  have hf : WidthFollows base scanLoadOps s := by
    simp [scanLoadOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = scanLoadOps.length by rfl, width_run base scanLoadOps s hc he ha hf]
  simp only [NatCompare.saved] at hread hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases hd : reg = 11#5 <;> by_cases ht : reg = 9#5 <;>
        by_cases hsp : reg = 31#5 <;> (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
            NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
          NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
          BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg => simp [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect,
        put, next, Dispatch.next, NatCompare.saved, state_simp_rules]
    | FLAG flag => simp [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect,
        put, next, Dispatch.next, NatCompare.saved, state_simp_rules]
    | ERR => simp [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect,
        put, next, Dispatch.next, NatCompare.saved, state_simp_rules]
  · simp [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect, put, next,
      Dispatch.next, NatCompare.saved, state_simp_rules]
  · intro n addr
    simp [scanLoadResult, scanLoadOps, widthBlock, WidthOp.effect, put, next,
      Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

theorem scan_load_frame (s : ArmState) (base limb : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (scanLoadResult s base limb) := by
  have hf := NatNarrow.saved_frame s 9#5 hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [scanLoadResult, state_simp_rules] using hf.program
  · simpa [scanLoadResult, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [scanLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [scanLoadResult, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [scanLoadResult, state_simp_rules] using hf.memory a ha

end SszArm.Emit.Uint
