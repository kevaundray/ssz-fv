import SszX86.Udivti3Control

namespace SszX86.Udivti3

set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

/-- Full SysV postcondition after RET. Every byte of data memory and every SIMD
register is unchanged; RSP advances by exactly eight, and all callee-saved GPRs
are unchanged. The result is the complete unsigned 128-bit quotient RDX:RAX. -/
structure Returned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec ra
  quotient : value t.1.regs.rax.toBitVec t.1.regs.rdx.toBitVec = numerator s / denominator s
  memory : t.1.dmem = s.dmem
  vectors : t.1.zmms = s.zmms
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8#64
  saved : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi →
    r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r

@[simp] theorem returned_status (s : MachineData) (status : StatusFlags) (ra : BitVec 64) :
    Returned { s with status } ra = Returned s ra := by
  funext st
  apply propext
  constructor <;> intro h
  · exact ⟨h.pc, h.quotient, h.memory, h.vectors, h.stack, h.saved⟩
  · exact ⟨h.pc, h.quotient, h.memory, h.vectors, h.stack, h.saved⟩

private theorem return_correct (base : Int64) (s t : MachineData) (ra : BitVec 64)
    (off : Nat) (hoff : off = 108 ∨ off = 184 ∨ off = 191 ∨ off = 196)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hf : Frame s t)
    (hq : value t.regs.rax.toBitVec t.regs.rdx.toBitVec = numerator s / denominator s) :
    Eventually (step base) (Returned s ra) (t, base + Int64.ofNat off) := by
  apply ret_runs base t ra off hoff
  · simpa only [hf.memory, hf.stack] using hr
  · refine ⟨rfl, hq, hf.memory, hf.vectors, ?_, ?_⟩
    · change t.regs.rsp.toBitVec + 8#64 = s.regs.rsp.toBitVec + 8#64
      rw [hf.stack]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      have h := hf.saved r h1 h2 h3 h4 h5 h6 h7 h8 h9
      cases r <;> simp_all [Reg64s.get64]

private theorem finish_word (base : Int64) (s t : MachineData) (ra : BitVec 64)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hf : Frame s t) (hflag : t.regs.r10.toBitVec = 0)
    (hq : t.regs.r8.toBitVec.toNat * radix + t.regs.rax.toBitVec.toNat =
      numerator s / denominator s) :
    Eventually (step base) (Returned s ra) (t, base + 100) := by
  apply word_exit_runs
  intro status
  simp only [hflag, ↓reduceIte]
  exact return_correct base s (wordExit t status) ra 108 (by simp) hr
    (hf.trans (wordExit_frame t status)) hq

/-- The wide-divisor path uses all 64 low-input bits and returns a one-limb
quotient. No initial remainder bound stronger than input representability is used. -/
theorem wide_correct (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hw : s.regs.rcx.toBitVec ≠ 0)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra) (s, base + 128) := by
  have hd : 0 < denominator s := by
    have hhi : 0 < s.regs.rcx.toBitVec.toNat := by
      have hz : s.regs.rcx.toBitVec.toNat ≠ 0 := by
        intro h
        apply hw
        apply BitVec.eq_of_toNat_eq
        simpa using h
      omega
    simp only [denominator, value, radix]
    omega
  apply wide_setup_runs
  intro status
  let t := wideStart s status
  have hi : Invariant true (denominator s) (numerator s) 64 t := by
    exact wide_invariant t rfl rfl rfl hw
  have hrun := loop_runs base true (denominator s) (numerator s) hd
    (value_lt s.regs.rdi.toBitVec s.regs.rsi.toBitVec) 64 t (by decide) hi
  apply eventually_trans _ _ _ _ hrun
  rintro ⟨u, pc⟩ hu
  have hpc : pc = base + 182 := hu.pc
  subst pc
  apply wide_exit_runs
  intro status'
  apply return_correct base s (wideExit u status') ra 184 (by simp) hr
    ((wideStart_frame s status).trans (hu.frame.toFrame.trans (wideExit_frame u status')))
  simpa [wideExit, value] using hu.quotient

/-- A one-pass word division when the incoming high numerator limb is below the
one-word divisor. R8 is the zero high quotient selected by the entry sequence. -/
private theorem word_single_correct (base : Int64) (s : MachineData) (ra : BitVec 64)
    (status : StatusFlags) (hw : s.regs.rcx.toBitVec = 0)
    (hd : 0 < s.regs.rdx.toBitVec.toNat)
    (hh : s.regs.rsi.toBitVec.toNat < s.regs.rdx.toBitVec.toNat)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra) (wordStart s false status, base + 71) := by
  let t := wordStart s false status
  have hi : Invariant false s.regs.rdx.toBitVec.toNat (numerator s) 64 t := by
    exact word_invariant t s.regs.rsi.toBitVec.toNat rfl rfl rfl hh
  have hrun := loop_runs base false s.regs.rdx.toBitVec.toNat (numerator s) hd
    (value_lt s.regs.rdi.toBitVec s.regs.rsi.toBitVec) 64 t (by decide) hi
  apply eventually_trans _ _ _ _ hrun
  rintro ⟨u, pc⟩ hu
  have hpc : pc = base + 100 := hu.pc
  subst pc
  have hflag : u.regs.r10.toBitVec = 0 := by
    rw [(hu.frame.wordLive rfl).2]
    rfl
  have hhigh : u.regs.r8.toBitVec.toNat = 0 := by
    rw [hu.frame.highQuotient]
    rfl
  apply finish_word base s u ra hr ((wordStart_frame s false status).trans hu.frame.toFrame) hflag
  simpa [hhigh, denominator, hw, value] using hu.quotient

/-- Two complete word passes. The first remainder is carried into the second;
its quotient is kept in R8 across the second pass and moved to RDX before RET. -/
private theorem word_double_correct (base : Int64) (s : MachineData) (ra : BitVec 64)
    (status : StatusFlags) (hw : s.regs.rcx.toBitVec = 0)
    (hd : 0 < s.regs.rdx.toBitVec.toNat)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra) (wordStart s true status, base + 71) := by
  let d := s.regs.rdx.toBitVec.toNat
  let hi := s.regs.rsi.toBitVec.toNat
  let lo := s.regs.rdi.toBitVec.toNat
  let t := wordStart s true status
  have hi0 : Invariant false d hi 64 t := by
    simpa [t, wordStart, hi, d] using word_invariant t 0 rfl rfl rfl hd
  have hbound : hi < radix * radix := by
    have h := s.regs.rsi.toBitVec.isLt
    dsimp [hi, radix] at *
    omega
  have hrun := loop_runs base false d hi hd hbound 64 t (by decide) hi0
  apply eventually_trans _ _ _ _ hrun
  rintro ⟨u, pc⟩ hu
  have hpc : pc = base + 100 := hu.pc
  subst pc
  have hframe : Frame s u := (wordStart_frame s true status).trans hu.frame.toFrame
  have hflag : u.regs.r10.toBitVec = 1 := by
    rw [(hu.frame.wordLive rfl).2]
    rfl
  have hlow : u.regs.rdi = s.regs.rdi := (hu.frame.wordLive rfl).1
  have hdiv : u.regs.rdx = s.regs.rdx := hu.frame.lowDivisor
  have hrem : u.regs.r9.toBitVec.toNat = hi % d := by
    have hc : u.regs.rax.toBitVec.toNat * d + u.regs.r9.toBitVec.toNat = hi := hu.conservation
    have hb : u.regs.r9.toBitVec.toNat < d := hu.remainder_lt
    rw [← hc]
    exact (Nat.mul_add_mod_of_lt hb).symm
  apply word_exit_runs
  intro af
  simp only [hflag]
  let v : MachineData := { u with status := af }
  have hfv : Frame s v := hframe.trans (status_frame u af)
  apply second_runs
  intro af'
  let w := secondStart v af'
  let n := (hi % d) * radix + lo
  have hi1 : Invariant false d n 64 w := by
    have hrem' : w.regs.r9.toBitVec.toNat = hi % d := hrem
    have hdiv' : w.regs.rdx.toBitVec.toNat = d := congrArg (fun x : UInt64 => x.toBitVec.toNat) hdiv
    have hsource : w.regs.rsi.toBitVec.toNat = lo := congrArg (fun x : UInt64 => x.toBitVec.toNat) hlow
    have hb : hi % d < w.regs.rdx.toBitVec.toNat := by
      rw [hdiv']
      exact Nat.mod_lt _ hd
    simpa only [hdiv', hsource] using word_invariant w (hi % d) rfl rfl hrem' hb
  have hn : n < radix * radix := by
    have hb := value_lt w.regs.rsi.toBitVec w.regs.r9.toBitVec
    simpa [value, w, secondStart, v, hrem, hlow, n, lo] using hb
  have hrun2 := loop_runs base false d n hd hn 64 w (by decide) hi1
  apply eventually_trans _ _ _ _ hrun2
  rintro ⟨z, pc⟩ hz
  have hpc : pc = base + 100 := hz.pc
  subst pc
  have hfz : Frame s z := hfv.trans ((secondStart_frame v af').trans hz.frame.toFrame)
  have hflagz : z.regs.r10.toBitVec = 0 := by
    rw [(hz.frame.wordLive rfl).2]
    rfl
  have hhigh : z.regs.r8.toBitVec.toNat = hi / d := by
    rw [hz.frame.highQuotient]
    exact hu.quotient
  apply finish_word base s z ra hr hfz hflagz
  rw [hhigh, hz.quotient]
  simpa [n, numerator, denominator, value, hw, hi, lo, d] using
    SszNative.Division.two_word_quotient d hi lo radix hd

/-- The complete one-word-divisor path, without any quotient-fit restriction. -/
theorem word_correct (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hw : s.regs.rcx.toBitVec = 0) (hd : 0 < denominator s)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra) (s, base + 35) := by
  have hd' : 0 < s.regs.rdx.toBitVec.toNat := by
    simpa [denominator, value, hw] using hd
  apply word_setup_runs
  intro status
  by_cases hh : s.regs.rdx.toBitVec.toNat ≤ s.regs.rsi.toBitVec.toNat
  · simpa only [hh, decide_true] using word_double_correct base s ra status hw hd' hr
  · simpa only [hh, decide_false] using word_single_correct base s ra status hw hd' (by omega) hr

/-- Complete execution of the actual 197-byte `__udivti3` implementation at an
arbitrary code base, for every nonzero 128-bit divisor. Only the eight-byte RET
slot must be mapped. All undefined flags are universally quantified by Kraken's
omnisemantics; there is no stack scratch, input-memory hypothesis, or width
restriction on the divisor or quotient. -/
theorem program_correct (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hd : 0 < denominator s)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra) (s, base) := by
  apply entry_runs
  intro status
  let t : MachineData := { s with status }
  by_cases hsmall : numerator s < denominator s
  · simp only [hsmall, ↓reduceIte]
    apply zero_runs
    intro status'
    apply return_correct base s (zeroState t status') ra 196 (by simp) hr
      ((status_frame s status).trans (zeroState_frame t status'))
    simp [zeroState, value, Nat.div_eq_of_lt hsmall]
  · simp only [hsmall, ↓reduceIte]
    apply dispatch_runs
    intro status'
    let u : MachineData := { t with status := status' }
    change Eventually (step base) (Returned s ra) (u,
      if s.regs.rcx.toBitVec ≠ 0 then base + 128
      else if s.regs.rdx.toBitVec = 1 then base + 185 else base + 35)
    by_cases hw : s.regs.rcx.toBitVec = 0
    · rw [ite_eq_right (fun h => h hw)]
      by_cases ho : s.regs.rdx.toBitVec = 1
      · rw [ite_eq_left ho]
        apply one_runs
        apply return_correct base s (oneState u) ra 191 (by simp) hr
          ((status_frame s status').trans (oneState_frame u))
        simp [oneState, u, t, numerator, denominator, value, hw, ho]
      · rw [ite_eq_right ho]
        simpa [u, t, numerator, denominator] using word_correct base u ra hw hd hr
    · rw [ite_eq_left hw]
      simpa [u, t, numerator, denominator] using wide_correct base u ra hw hr

end SszX86.Udivti3
