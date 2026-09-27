import SszArm.Udivti3Loops

namespace SszArm.Udivti3

open BitVec
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

@[simp] theorem block_lr (ks : List Nat) (s : ArmState) :
    r (.GPR 30) (block ks s) = r (.GPR 30) s :=
  block_frame ks s (.GPR 30) (by decide)

@[simp] theorem block_dlo (ks : List Nat) (s : ArmState) :
    r (.GPR 2) (block ks s) = r (.GPR 2) s :=
  block_frame ks s (.GPR 2) (by decide)

@[simp] theorem block_dhi (ks : List Nat) (s : ArmState) :
    r (.GPR 3) (block ks s) = r (.GPR 3) s :=
  block_frame ks s (.GPR 3) (by decide)

@[simp] theorem block_divisor (ks : List Nat) (s : ArmState) :
    divisor (block ks s) = divisor s := by simp only [divisor, block_dlo, block_dhi]

private theorem entry_block (s : ArmState) : block (entryTrace s) s = entry s := rfl

/-- One 64-bit pass, with the actual carry-aware word loop. -/
theorem word_pass (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+88#64) (hn : r (.GPR 7) s = 64#64)
    (hq : r (.GPR 0) s = 0#64)
    (hr : (r (.GPR 6) s).toNat < (r (.GPR 2) s).toNat) :
    let t := block (wordLoopTrace 64 s) s
    Follows base (wordLoopTrace 64 s) s ∧ read_pc t = base+128#64 ∧
    (r (.GPR 7) t).toNat = 0 ∧
    (r (.GPR 0) t).toNat =
      ((r (.GPR 6) s).toNat*radix+(r (.GPR 5) s).toNat)/(r (.GPR 2) s).toNat ∧
    (r (.GPR 6) t).toNat =
      ((r (.GPR 6) s).toNat*radix+(r (.GPR 5) s).toNat)%(r (.GPR 2) s).toNat ∧
    r (.GPR 1) t = r (.GPR 1) s ∧ r (.GPR 4) t = r (.GPR 4) s ∧
    r (.GPR 8) t = r (.GPR 8) s := by
  have h := word_loop 64 s base (r (.GPR 5) s) (by decide)
    (by rw [hn]; decide) (by simpa using hp) (by simp [pending_full]) (by rw [hq]; decide) hr
  have hd : 0 < (r (.GPR 2) s).toNat := by omega
  simpa only [hq, BitVec.toNat_ofNat, Nat.zero_mod,
    Division.loop_quotient _ _ 64 _ (r (.GPR 5) s).isLt hr hd,
    Division.loop_remainder _ _ 64 _ (r (.GPR 5) s).isLt hr hd] using h

/-- One wide pass; its only prefix-bound premise is that the starting high
input word is representable, not that the full divisor is a single word. -/
theorem wide_pass (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+180#64) (hn : r (.GPR 7) s = 64#64)
    (hq : r (.GPR 0) s = 0#64)
    (hr : join (r (.GPR 5) s) (r (.GPR 6) s) < divisor s)
    (hb : join (r (.GPR 5) s) (r (.GPR 6) s) < radix) :
    let t := block (wideLoopTrace 64 s) s
    Follows base (wideLoopTrace 64 s) s ∧ read_pc t = base+236#64 ∧
    (r (.GPR 7) t).toNat = 0 ∧
    (r (.GPR 0) t).toNat =
      (join (r (.GPR 5) s) (r (.GPR 6) s)*radix+(r (.GPR 4) s).toNat)/divisor s ∧
    join (r (.GPR 5) t) (r (.GPR 6) t) =
      (join (r (.GPR 5) s) (r (.GPR 6) s)*radix+(r (.GPR 4) s).toNat)%divisor s ∧
    r (.GPR 1) t = r (.GPR 1) s := by
  have h := wide_loop 64 s base (r (.GPR 4) s) (by decide)
    (by rw [hn]; decide) (by simpa using hp) (by simp [pending_full]) (by rw [hq]; decide) hr hb
  have hd : 0 < divisor s := by omega
  simpa only [hq, BitVec.toNat_ofNat, Nat.zero_mod,
    Division.loop_quotient _ _ 64 _ (r (.GPR 4) s).isLt hr hd,
    Division.loop_remainder _ _ 64 _ (r (.GPR 4) s).isLt hr hd] using h

theorem word_return (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+128#64) (hh : r (.GPR 8) s = 0#64) :
    Follows base [32,39] s ∧
    read_pc (block [32,39] s) = r (.GPR 30) s ∧
    numerator (block [32,39] s) = numerator s := by
  change r .PC s = base+128#64 at hp
  simp_all (config := {decide := true, instances := true})
    [block, Follows, instruction, branch, state_simp_rules,
     numerator, BitVec.add_assoc]
  all_goals bv_omega

theorem wide_return (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+236#64) :
    Follows base [59,60] s ∧
    read_pc (block [59,60] s) = r (.GPR 30) s ∧
    numerator (block [59,60] s) = (r (.GPR 0) s).toNat := by
  change r .PC s = base+236#64 at hp
  simp (config := {decide := true, instances := true})
    [block, Follows, instruction, next, put, state_simp_rules,
     hp, numerator, join_eq, BitVec.add_assoc]
  all_goals bv_omega

theorem zero_return (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+248#64) :
    Follows base [62,63,64] s ∧
    read_pc (block [62,63,64] s) = r (.GPR 30) s ∧
    numerator (block [62,63,64] s) = 0 := by
  change r .PC s = base+248#64 at hp
  simp (config := {decide := true, instances := true})
    [block, Follows, instruction, next, put, state_simp_rules,
     hp, numerator, join_eq, BitVec.add_assoc]
  all_goals bv_omega

theorem one_return (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+20#64) (hh : r (.GPR 3) s = 0#64)
    (hd : r (.GPR 2) s = 1#64) :
    Follows base [5,6,7,61] s ∧
    read_pc (block [5,6,7,61] s) = r (.GPR 30) s ∧
    numerator (block [5,6,7,61] s) = numerator s := by
  change r .PC s = base+20#64 at hp
  simp_all (config := {decide := true, instances := true})
    [block, Follows, instruction, next, compare, branch, state_simp_rules,
     numerator, BitVec.add_assoc]
  all_goals bv_omega

def wordPath (s : ArmState) : List Nat :=
  let a := block (wordSetup s) s
  let b := block (wordLoopTrace 64 a) a
  wordSetup s ++ wordLoopTrace 64 a ++
    if (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat then [32,39]
    else
      let c := block [32,33,34,35,36,37,38] b
      [32,33,34,35,36,37,38] ++ wordLoopTrace 64 c ++ [32,39]

def widePath (s : ArmState) : List Nat :=
  let a := block [5,40,41,42,43,44] s
  [5,40,41,42,43,44] ++ wideLoopTrace 64 a ++ [59,60]

theorem word_path_correct (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+20#64) (hh : r (.GPR 3) s = 0#64)
    (hd : r (.GPR 2) s ≠ 1#64) (hpos : 0 < (r (.GPR 2) s).toNat) :
    Follows base (wordPath s) s ∧ read_pc (block (wordPath s) s) = r (.GPR 30) s ∧
    numerator (block (wordPath s) s) = numerator s / divisor s := by
  let a := block (wordSetup s) s
  let b := block (wordLoopTrace 64 a) a
  have ha := word_setup s base hp hh hd
  change Follows base (wordSetup s) s ∧ read_pc a = _ ∧ _ at ha
  have had : r (.GPR 2) a = r (.GPR 2) s := block_dlo _ _
  have halr : r (.GPR 30) a = r (.GPR 30) s := block_lr _ _
  have hblr : r (.GPR 30) b = r (.GPR 30) s := (block_lr _ _).trans halr
  have hdiv : divisor s = (r (.GPR 2) s).toNat := by
    rw [divisor, hh, join_eq]
    simp
  by_cases hshort : (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat
  · simp only [hshort, ↓reduceIte] at ha
    rcases ha with ⟨haf, hap, haq, ha1, ha4, ha7, ha5, ha6, ha8⟩
    have har : (r (.GPR 6) a).toNat < (r (.GPR 2) a).toNat := by
      rw [ha6, had]
      exact hshort
    obtain ⟨hbf, hbp, hb7, hbq, hbr, hb1, hb4, hb8⟩ := word_pass a base hap ha7 haq har
    have hz : r (.GPR 8) b = 0#64 := hb8.trans ha8
    obtain ⟨hretf, hretpc, hretq⟩ := word_return b base hbp hz
    have hstate : block (wordPath s) s = block [32,39] b := by
      simp only [wordPath, hshort, ↓reduceIte, block_append]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · simpa only [wordPath, hshort, ↓reduceIte, follows_append, block_append, _root_.and_assoc]
        using And.intro haf (And.intro hbf hretf)
    · rw [hstate, hretpc, hblr]
    · rw [hstate, hretq]
      change join (r (.GPR 0) b) (r (.GPR 1) b) = _
      rw [show r (.GPR 1) b = 0#64 from hb1.trans ha1]
      simp only [join_eq, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
      rw [hbq, ha6, ha5, had, hdiv]
      simp only [numerator, join_eq]
  · simp only [hshort, ↓reduceIte] at ha
    rcases ha with ⟨haf, hap, haq, ha1, ha4, ha7, ha5, ha6, ha8⟩
    have har : (r (.GPR 6) a).toNat < (r (.GPR 2) a).toNat := by
      rw [ha6, had]
      exact hpos
    obtain ⟨hbf, hbp, hb7, hbq, hbr, hb1, hb4, hb8⟩ := word_pass a base hap ha7 haq har
    have hbq' : (r (.GPR 0) b).toNat = (r (.GPR 1) s).toNat/(r (.GPR 2) s).toNat := by
      rw [ha6, ha5, had] at hbq
      simpa only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add] using hbq
    have hbr' : (r (.GPR 6) b).toNat = (r (.GPR 1) s).toNat%(r (.GPR 2) s).toNat := by
      rw [ha6, ha5, had] at hbr
      simpa only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add] using hbr
    let c := block [32,33,34,35,36,37,38] b
    have hc := second_setup b base hbp (hb8.trans ha8)
    change Follows base [32,33,34,35,36,37,38] b ∧ read_pc c = _ ∧ _ at hc
    rcases hc with ⟨hcf, hcp, hcq, hc1, hc5, hc6, hc7, hc8⟩
    have hcd : r (.GPR 2) c = r (.GPR 2) s := by
      simp only [c, b, a, block_dlo]
    have hcr : (r (.GPR 6) c).toNat < (r (.GPR 2) c).toNat := by
      rw [hc6, hbr', hcd]
      exact Nat.mod_lt _ hpos
    let e := block (wordLoopTrace 64 c) c
    obtain ⟨hef, hep, he7, heq, her, he1, he4, he8⟩ := word_pass c base hcp hc7 hcq hcr
    obtain ⟨hretf, hretpc, hretq⟩ := word_return e base hep (he8.trans hc8)
    have hstate : block (wordPath s) s = block [32,39] e := by
      simp only [wordPath, hshort, ↓reduceIte, block_append]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · simpa only [wordPath, hshort, ↓reduceIte, follows_append, block_append, _root_.and_assoc]
        using And.intro haf (And.intro hbf (And.intro hcf (And.intro hef hretf)))
    · rw [hstate, hretpc]
      simp only [e, c, b, a, block_lr]
    · rw [hstate, hretq]
      change join (r (.GPR 0) e) (r (.GPR 1) e) = _
      rw [join_eq]
      rw [he1, hc1, hbq', heq, hc6, hbr', hc5, hb4, ha4, hcd, hdiv]
      simp only [numerator, join_eq]
      exact Division.two_word_quotient _ _ _ radix hpos

theorem wide_path_correct (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+20#64) (hh : r (.GPR 3) s ≠ 0#64) :
    Follows base (widePath s) s ∧ read_pc (block (widePath s) s) = r (.GPR 30) s ∧
    numerator (block (widePath s) s) = numerator s / divisor s := by
  let a := block [5,40,41,42,43,44] s
  let b := block (wideLoopTrace 64 a) a
  obtain ⟨haf, hap, haq, ha4, ha5, ha6, ha7⟩ := wide_setup s base hp hh
  have had : divisor a = divisor s := block_divisor _ _
  have har : join (r (.GPR 5) a) (r (.GPR 6) a) < divisor a := by
    rw [ha5, ha6, had]
    have hhi := (r (.GPR 1) s).isLt
    have hdh : 0 < (r (.GPR 3) s).toNat := by bv_omega
    simp only [divisor, join_eq, radix, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.zero_mul, Nat.zero_add]
    omega
  have hab : join (r (.GPR 5) a) (r (.GPR 6) a) < radix := by
    rw [ha5, ha6, join_eq]
    simpa only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add] using
      (r (.GPR 1) s).isLt
  obtain ⟨hbf, hbp, hb7, hbq, hbr, hb1⟩ := wide_pass a base hap ha7 haq har hab
  obtain ⟨hretf, hretpc, hretq⟩ := wide_return b base hbp
  have hstate : block (widePath s) s = block [59,60] b := by
    simp only [widePath, block_append]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [widePath, follows_append, block_append, _root_.and_assoc] using
      And.intro haf (And.intro hbf hretf)
  · rw [hstate, hretpc]
    simp only [b, a, block_lr]
  · rw [hstate, hretq, hbq, ha5, ha6, ha4, had]
    simp only [numerator, join_eq, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.zero_mul, Nat.zero_add]

/-- A complete finite instruction path selected solely from the input registers.
Both passes and every actual return instruction are retained in this path. -/
def trace (s : ArmState) : List Nat :=
  entryTrace s ++
    if numerator s < divisor s then [62,63,64]
    else if r (.GPR 3) s ≠ 0#64 then widePath (entry s)
    else if r (.GPR 2) s = 1#64 then [5,6,7,61]
    else wordPath (entry s)

def result (s : ArmState) : ArmState := block (trace s) s

def fuel (s : ArmState) : Nat := (trace s).length

/-- No nonzero divisor case is excluded: early-zero, divisor-one, a single word
pass, two word passes, and a genuine two-word divisor all meet the same result. -/
theorem trace_correct (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base) (hd : 0 < divisor s) :
    Follows base (trace s) s ∧ read_pc (result s) = r (.GPR 30) s ∧
    numerator (result s) = numerator s / divisor s := by
  obtain ⟨hef, hep, her⟩ := entry_data s base hp
  have hn : numerator (entry s) = numerator s := by simp only [numerator, her]
  have hdiv : divisor (entry s) = divisor s := by simp only [divisor, her]
  have hlr : r (.GPR 30) (entry s) = r (.GPR 30) s := her 30
  by_cases hzero : numerator s < divisor s
  · have hep' : read_pc (entry s) = base+248#64 := by simpa only [hzero, ↓reduceIte] using hep
    obtain ⟨htf, htp, htq⟩ := zero_return (entry s) base hep'
    refine ⟨?_, ?_, ?_⟩
    · simpa only [trace, hzero, ↓reduceIte, follows_append, entry_block] using And.intro hef htf
    · simpa only [result, trace, hzero, ↓reduceIte, block_append, entry_block] using htp.trans hlr
    · simpa only [result, trace, hzero, ↓reduceIte, block_append,
        entry_block, Nat.div_eq_of_lt hzero] using htq
  · have hep' : read_pc (entry s) = base+20#64 := by simpa only [hzero, ↓reduceIte] using hep
    by_cases hwide : r (.GPR 3) s ≠ 0#64
    · obtain ⟨htf, htp, htq⟩ := wide_path_correct (entry s) base hep'
        (by simpa only [her] using hwide)
      have htrace : trace s = entryTrace s ++ widePath (entry s) := by
        unfold trace
        rw [if_neg hzero, if_pos hwide]
      refine ⟨?_, ?_, ?_⟩
      · simpa only [htrace, follows_append, entry_block] using And.intro hef htf
      · simpa only [result, htrace, block_append, entry_block] using htp.trans hlr
      · simpa only [result, htrace, block_append, entry_block, hn, hdiv] using htq
    · have hh : r (.GPR 3) s = 0#64 := by simpa using hwide
      by_cases hone : r (.GPR 2) s = 1#64
      · obtain ⟨htf, htp, htq⟩ := one_return (entry s) base hep'
          (by simpa only [her] using hh) (by simpa only [her] using hone)
        have hd1 : divisor s = 1 := by rw [divisor, hh, hone, join_eq]; decide
        refine ⟨?_, ?_, ?_⟩
        · simpa only [trace, hzero, hwide, hone, ↓reduceIte, follows_append, entry_block] using And.intro hef htf
        · simpa only [result, trace, hzero, hwide, hone, ↓reduceIte, block_append, entry_block] using htp.trans hlr
        · rw [hd1, Nat.div_one]
          simpa only [result, trace, hzero, hwide, hone, ↓reduceIte, block_append,
            entry_block, hn] using htq
      · have hpos : 0 < (r (.GPR 2) (entry s)).toNat := by
          simpa only [divisor, join_eq, hh, her, BitVec.toNat_ofNat,
            Nat.zero_mod, Nat.zero_mul, Nat.zero_add] using hd
        obtain ⟨htf, htp, htq⟩ := word_path_correct (entry s) base hep'
          (by simpa only [her] using hh) (by simpa only [her] using hone) hpos
        refine ⟨?_, ?_, ?_⟩
        · simpa only [trace, hzero, hwide, hone, ↓reduceIte, follows_append, entry_block] using And.intro hef htf
        · simpa only [result, trace, hzero, hwide, hone, ↓reduceIte, block_append, entry_block] using htp.trans hlr
        · simpa only [result, trace, hzero, hwide, hone, ↓reduceIte, block_append,
            entry_block, hn, hdiv] using htq

/-- Full pinned-model execution, fetching and executing every word through RET. -/
theorem program_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base) (he : read_err s = .None)
    (hd : 0 < divisor s) : run (fuel s) s = result s :=
  follows_run base (trace s) s hc he (trace_correct s base hp hd).1

theorem result_frame (s : ArmState) (f : StateField) (hf : Preserved f) :
    r f (result s) = r f s := block_frame (trace s) s f hf

theorem result_memory (s : ArmState) : (result s).mem = s.mem := block_memory (trace s) s

theorem result_program (s : ArmState) : (result s).program = s.program := block_program (trace s) s

theorem result_return (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base) (hd : 0 < divisor s) :
    read_pc (result s) = r (.GPR 30) s := (trace_correct s base hp hd).2.1

theorem result_quotient (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base) (hd : 0 < divisor s) :
    numerator (result s) = numerator s / divisor s := (trace_correct s base hp hd).2.2

/-- Generic unsigned-128 division with no input-memory or stack precondition.
The complete memory, SP, LR, all SIMD registers, all callee-saved registers,
and the initial no-error state survive the actual return. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base) (he : read_err s = .None)
    (hd : 0 < join (r (.GPR 2) s) (r (.GPR 3) s)) :
    let final := run (fuel s) s
    join (r (.GPR 0) final) (r (.GPR 1) final) =
      join (r (.GPR 0) s) (r (.GPR 1) s) / join (r (.GPR 2) s) (r (.GPR 3) s) ∧
    read_err final = .None ∧ read_pc final = r (.GPR 30) s ∧
    final.mem = s.mem ∧ final.program = s.program ∧
    r (.GPR 31) final = r (.GPR 31) s ∧ r (.GPR 30) final = r (.GPR 30) s ∧
    (∀ i, r (.SFP i) final = r (.SFP i) s) ∧
    (∀ f, Preserved f → r f final = r f s) := by
  dsimp only
  rw [program_run s base hc hp he hd]
  refine ⟨result_quotient s base hp hd, (result_frame s .ERR trivial).trans he,
    result_return s base hp hd, result_memory s, result_program s,
    result_frame s (.GPR 31) (by decide), result_frame s (.GPR 30) (by decide),
    fun i => result_frame s (.SFP i) trivial, result_frame s⟩

end SszArm.Udivti3
