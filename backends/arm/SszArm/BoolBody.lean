import SszArm.BoolTails

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def inputByte (s : ArmState) : BitVec 8 := read_mem_bytes 1 (r (.GPR 2) s) s

def bodySteps (s : ArmState) : Nat :=
  if r (.GPR 3) s = 1#64 then
    if inputByte s = 0#8 then 37 else if inputByte s = 1#8 then 39 else 56
  else 51

def bodyState (s : ArmState) (base : BitVec 64) : ArmState :=
  let l := lengthCompared s
  if r (.GPR 3) s = 1#64 then
    let b := byteLoaded (w .PC (base + 612#64) l)
    if inputByte s = 0#8 then successTail falseStores (w .PC (base + 4084#64) b) base
    else
      let c := byteCompared (w .PC (base + 620#64) b)
      if inputByte s = 1#8 then successTail trueStores (w .PC (base + 628#64) c) base
      else badTail (w .PC (base + 4144#64) c) base
  else returned (afterJump scopeStores (w .PC (base + 2084#64) l) base 4732)

/-- Every selected actual instruction, including lowering scratch operations and RET. -/
theorem body_run (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 604#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run (bodySteps s) s = bodyState s base := by
  let l := lengthCompared s
  have hlc : CodeAt l base := by
    simpa [l, CodeAt, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules] using hc
  have hle : read_err l = .None := by
    simpa [l, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules] using he
  have hla : CheckSPAlignment l := by
    simpa [l, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules] using ha
  by_cases hn : r (.GPR 3) s = 1#64
  · let t := w .PC (base + 612#64) l
    have htc : CodeAt t base := by simpa [t, CodeAt, state_simp_rules] using hlc
    have hte : read_err t = .None := by simpa [t, state_simp_rules] using hle
    have hta : CheckSPAlignment t := by simpa [t, state_simp_rules] using hla
    have htpc : read_pc t = base + 612#64 := by simp [t, state_simp_rules]
    have htbyte : read_mem_bytes 1 (r (.GPR 2) t) t = inputByte s := by
      simp [t, l, inputByte, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules]
    let b := byteLoaded t
    have hbc : CodeAt b base := by simpa [b, CodeAt, byteLoaded, state_simp_rules] using htc
    have hbe : read_err b = .None := by simpa [b, byteLoaded, state_simp_rules] using hte
    have hba : CheckSPAlignment b := by simpa [b, byteLoaded, state_simp_rules] using hta
    have hload : run 4 s = w .PC
        (if inputByte s = 0#8 then base + 4084#64 else base + 620#64) b := by
      rw [show 4 = 2 + 2 by decide, run_plus, length_branch s base hc hp he]
      simp only [hn, ↓reduceIte]
      rw [byte_zero_branch t base htc htpc hte, htbyte]
    by_cases hz : inputByte s = 0#8
    · simp only [bodySteps, bodyState, hn, hz, ↓reduceIte]
      rw [show 37 = 4 + 33 by decide, run_plus, hload]
      simp only [hz, ↓reduceIte]
      apply false_tail _ base
      · simpa [CodeAt, state_simp_rules] using hbc
      · simp [state_simp_rules]
      · simpa [state_simp_rules] using hbe
      · simpa [state_simp_rules] using hba
    · let u := w .PC (base + 620#64) b
      have huc : CodeAt u base := by simpa [u, CodeAt, state_simp_rules] using hbc
      have hue : read_err u = .None := by simpa [u, state_simp_rules] using hbe
      have hua : CheckSPAlignment u := by simpa [u, state_simp_rules] using hba
      have hupc : read_pc u = base + 620#64 := by simp [u, state_simp_rules]
      have huone : (r (.GPR 8) u).setWidth 32 = 1#32 ↔ inputByte s = 1#8 := by
        simp (config := {decide := true}) only [u, b, byteLoaded, state_simp_rules, htbyte]
        bv_omega
      let c := byteCompared u
      have hcc : CodeAt c base := by simpa [c, CodeAt, byteCompared, state_simp_rules] using huc
      have hce : read_err c = .None := by simpa [c, byteCompared, state_simp_rules] using hue
      have hca : CheckSPAlignment c := by simpa [c, byteCompared, state_simp_rules] using hua
      have hcmp : run 6 s = w .PC
          (if inputByte s = 1#8 then base + 628#64 else base + 4144#64) c := by
        rw [show 6 = 4 + 2 by decide, run_plus, hload]
        simp only [hz, ↓reduceIte]
        rw [byte_one_branch u base huc hupc hue]
        simp only [huone]
        rfl
      by_cases ho : inputByte s = 1#8
      · simp only [bodySteps, bodyState, hn, hz, ↓reduceIte]
        simp only [ho, ↓reduceIte]
        rw [show 39 = 6 + 33 by decide, run_plus, hcmp]
        simp only [ho, ↓reduceIte]
        apply true_tail _ base
        · simpa [CodeAt, state_simp_rules] using hcc
        · simp [state_simp_rules]
        · simpa [state_simp_rules] using hce
        · simpa [state_simp_rules] using hca
      · simp only [bodySteps, bodyState, hn, hz, ho, ↓reduceIte]
        rw [show 56 = 6 + 50 by decide, run_plus, hcmp]
        simp only [ho, ↓reduceIte]
        apply bad_tail _ base
        · simpa [CodeAt, state_simp_rules] using hcc
        · simp [state_simp_rules]
        · simpa [state_simp_rules] using hce
        · simpa [state_simp_rules] using hca
  · simp only [bodySteps, bodyState, hn, ↓reduceIte]
    rw [show 51 = 2 + 49 by decide, run_plus, length_branch s base hc hp he]
    simp only [hn, ↓reduceIte]
    apply scope_tail _ base
    · simpa [CodeAt, state_simp_rules] using hlc
    · simp [state_simp_rules]
    · simpa [state_simp_rules] using hle
    · simpa [state_simp_rules] using hla

end SszArm.BoolCodec
