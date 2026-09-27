import SszX86.Udivti3Exec

namespace SszX86.Udivti3

set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

/-- The next input bit and remaining shifted word partition the unconsumed input. -/
theorem feed_partition (x : BitVec 64) (k : Nat) (hk : 0 < k) (hb : k ≤ 64) :
    bit x * 2 ^ (k - 1) + (x + x).toNat / 2 ^ (64 - (k - 1)) =
      x.toNat / 2 ^ (64 - k) := by
  let p := 2^(64-k)
  let t := 2^(k-1)
  have hp : p*t = 2^63 := by
    dsimp [p, t]
    have he : 64-k+(k-1) = 63 := by omega
    rw [← Nat.pow_add, he]
  have hr : radix = (2*p)*t := by rw [Nat.mul_assoc, hp]
  have hs : 2^(64-(k-1)) = 2*p := by
    have he : 64-(k-1) = (64-k)+1 := by omega
    dsimp [p]
    rw [he, Nat.pow_succ, Nat.mul_comm]
  simp only [bit, BitVec.toNat_add]
  change (2*x.toNat/radix)*t + (x.toNat+x.toNat)%radix/2^(64-(k-1)) = x.toNat/p
  rw [← Nat.two_mul, hr, hs, Nat.mod_mul_right_div_self,
    Nat.mul_div_mul_left x.toNat p (by decide : 0 < 2)]
  rw [Nat.mul_assoc, Nat.mul_div_mul_left x.toNat (p*t) (by decide : 0 < 2),
    ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' _ _

/-- No quotient ADD can overflow while a bit remains to be consumed. -/
theorem quotient_step_bound (d b q r k : Nat) (hk : 0 < k) (hb : k ≤ 64)
    (hq : q < 2 ^ (64 - k)) :
    (SszNative.Division.step d b q r).1 < 2 ^ (64 - (k - 1)) ∧
      (SszNative.Division.step d b q r).1 < radix := by
  have he : 64-(k-1) = (64-k)+1 := by omega
  have hq' : 2*q+1 < 2^(64-(k-1)) := by
    rw [he, Nat.pow_succ]
    omega
  have hp : 2^(64-(k-1)) ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
  unfold SszNative.Division.step
  dsimp only [radix]
  split <;> dsimp only <;> omega

/-- The consumed prefix, not a strengthened divisor precondition, prevents a
128-bit overflow in the two-limb ADC chain. -/
theorem tentative_bound (d n q r k : Nat) (x : BitVec 64)
    (hk : 0 < k) (_hb : k ≤ 64) (hn : n < radix * radix)
    (he : (q * d + r) * 2 ^ k + x.toNat / 2 ^ (64 - k) = n) :
    2 * r + bit x < radix * radix := by
  have hbit := bit_lt x
  have hp : 2^1 ≤ 2^k := Nat.pow_le_pow_right (by decide) (show 1 ≤ k by omega)
  have hr := Nat.mul_le_mul_right (2^k) (Nat.le_add_left r (q*d))
  have hdouble : 2*r ≤ r*2^k := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left r hp
  have hrn : r*2^k ≤ n := calc
    r*2^k ≤ (q*d+r)*2^k := hr
    _ ≤ (q*d+r)*2^k + x.toNat/2^(64-k) := Nat.le_add_right _ _
    _ = n := he
  have hbound := Nat.lt_of_le_of_lt (Nat.le_trans hdouble hrn) hn
  dsimp only [radix] at hbound ⊢
  omega

theorem advance_conservation (d q r q' r' n k : Nat) (x : BitVec 64)
    (hk : 0 < k) (hb : k ≤ 64)
    (he : (q * d + r) * 2 ^ k + x.toNat / 2 ^ (64 - k) = n)
    (hstep : q' * d + r' = 2 * (q * d + r) + bit x) :
    (q' * d + r') * 2 ^ (k - 1) + (x + x).toNat / 2 ^ (64 - (k - 1)) = n := by
  have hf := feed_partition x k hk hb
  have hp : 2^k = 2*2^(k-1) := by
    calc
      2^k = 2^((k-1)+1) := congrArg (2^·) (by omega)
      _ = 2*2^(k-1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hstep, Nat.add_mul]
  rw [show (2*(q*d+r))*2^(k-1) = (q*d+r)*2^k by rw [hp]; ac_rfl]
  omega

def source (wide : Bool) (s : MachineData) : BitVec 64 :=
  if wide then s.regs.rdi.toBitVec else s.regs.rsi.toBitVec

def remainder (wide : Bool) (s : MachineData) : Nat :=
  if wide then value s.regs.r9.toBitVec s.regs.r10.toBitVec else s.regs.r9.toBitVec.toNat

def divisor (wide : Bool) (s : MachineData) : Nat :=
  if wide then value s.regs.rdx.toBitVec s.regs.rcx.toBitVec else s.regs.rdx.toBitVec.toNat

def body (wide : Bool) (s : MachineData) : MachineData :=
  if wide then wideBody s else wordBody s

def loopPC (base : Int64) (wide : Bool) : Int64 :=
  if wide then base + 142 else base + 71

def endPC (base : Int64) (wide : Bool) : Int64 :=
  if wide then base + 182 else base + 100

/-- Additional live registers crossing a loop: both divisor limbs, saved high
quotient, and (on the word path) the original low input and pass selector. -/
structure LoopFrame (wide : Bool) (s t : MachineData) : Prop extends Frame s t where
  lowDivisor : t.regs.rdx = s.regs.rdx
  highDivisor : t.regs.rcx = s.regs.rcx
  highQuotient : t.regs.r8 = s.regs.r8
  wordLive : wide = false → t.regs.rdi = s.regs.rdi ∧ t.regs.r10 = s.regs.r10

theorem LoopFrame.refl (wide : Bool) (s : MachineData) : LoopFrame wide s s :=
  ⟨Frame.refl s, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem LoopFrame.trans {wide : Bool} {s t u : MachineData}
    (h : LoopFrame wide s t) (h' : LoopFrame wide t u) : LoopFrame wide s u := by
  refine ⟨h.toFrame.trans h'.toFrame, h'.lowDivisor.trans h.lowDivisor,
    h'.highDivisor.trans h.highDivisor, h'.highQuotient.trans h.highQuotient, ?_⟩
  intro hw
  exact ⟨(h'.wordLive hw).1.trans (h.wordLive hw).1,
    (h'.wordLive hw).2.trans (h.wordLive hw).2⟩

theorem body_frame (wide : Bool) (s : MachineData) : LoopFrame wide s (body wide s) := by
  cases wide
  · exact ⟨wordBody_frame s, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  · exact ⟨wideBody_frame s, rfl, rfl, rfl, by simp⟩

structure Invariant (wide : Bool) (d n k : Nat) (s : MachineData) : Prop where
  bounded : k ≤ 64
  count : s.regs.r11.toBitVec.toNat = k
  divisor_eq : divisor wide s = d
  remainder_lt : remainder wide s < d
  quotient_lt : s.regs.rax.toBitVec.toNat < 2 ^ (64 - k)
  conservation : (s.regs.rax.toBitVec.toNat * d + remainder wide s) * 2 ^ k +
    (source wide s).toNat / 2 ^ (64 - k) = n

/-- The machine iteration is the shared restoring-division step, on both widths. -/
theorem body_step (wide : Bool) (s : MachineData) (d n k : Nat)
    (hi : Invariant wide d n k s) (hk : 0 < k) (hn : n < radix * radix) :
    let p := SszNative.Division.step d (bit (source wide s))
      s.regs.rax.toBitVec.toNat (remainder wide s)
    (body wide s).regs.rax.toBitVec.toNat = p.1 ∧ remainder wide (body wide s) = p.2 := by
  have hq := quotient_step_bound d (bit (source wide s)) s.regs.rax.toBitVec.toNat
    (remainder wide s) k hk hi.bounded hi.quotient_lt
  have ht := tentative_bound d n s.regs.rax.toBitVec.toNat (remainder wide s) k
    (source wide s) hk hi.bounded hn hi.conservation
  have hb := bit_lt (source wide s)
  cases wide
  · have hd : s.regs.rdx.toBitVec.toNat = d := hi.divisor_eq
    have hr : s.regs.r9.toBitVec.toNat < s.regs.rdx.toBitVec.toNat := by
      simpa [remainder, ← hd] using hi.remainder_lt
    have htake := SszNative.DivisionBits.stepTake_iff (by decide)
      s.regs.r9.toBitVec s.regs.rdx.toBitVec (bit s.regs.rsi.toBitVec) hb
    have hrem := SszNative.DivisionBits.remainderStep_toNat (by decide)
      s.regs.r9.toBitVec s.regs.rdx.toBitVec (bit s.regs.rsi.toBitVec) hb hr
    by_cases hc : d ≤ 2 * s.regs.r9.toBitVec.toNat + bit s.regs.rsi.toBitVec
    all_goals
      simp only [SszNative.DivisionBits.stepNat, hd] at htake hrem
      simp_all [body, wordBody, source, remainder, SszNative.Division.step,
        BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod,
        Nat.two_mul, radix, ← Nat.not_lt, Nat.mod_eq_of_lt]
  · have ha := wide_adc s.regs.rdi.toBitVec s.regs.r9.toBitVec s.regs.r10.toBitVec ht
    have hd : value s.regs.rdx.toBitVec s.regs.rcx.toBitVec = d := hi.divisor_eq
    have ht' : value (wideLow s) (wideHigh s) =
        2 * remainder true s + bit (source true s) := ha
    have htake : wideTake s = decide (d ≤ 2 * remainder true s + bit (source true s)) := by
      simp only [wideTake_eq, hd, ht']
    by_cases hc : d ≤ 2 * remainder true s + bit (source true s)
    · have hsub := wide_sub (wideLow s) (wideHigh s) s.regs.rdx.toBitVec s.regs.rcx.toBitVec
        (by simpa only [hd, ht'] using hc)
      simp_all [body, wideBody, source, remainder, SszNative.Division.step,
        BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod,
        Nat.two_mul, radix, ← Nat.not_lt, Nat.mod_eq_of_lt]
    · simp_all [body, wideBody, source, remainder, SszNative.Division.step,
        BitVec.toNat_add, Nat.two_mul, radix, ← Nat.not_lt]

theorem body_invariant (wide : Bool) (s : MachineData) (d n k : Nat)
    (hi : Invariant wide d n k s) (hk : 0 < k) (hn : n < radix * radix) (hd : 0 < d) :
    Invariant wide d n (k - 1) (body wide s) := by
  let p := SszNative.Division.step d (bit (source wide s))
    s.regs.rax.toBitVec.toNat (remainder wide s)
  have hp := body_step wide s d n k hi hk hn
  have hs : source wide (body wide s) = source wide s + source wide s := by
    cases wide <;> rfl
  refine ⟨by have := hi.bounded; omega, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := hi.count
    have hb := hi.bounded
    cases wide <;> simp [body, wordBody, wideBody, BitVec.toNat_sub, hc] <;> omega
  · cases wide <;> exact hi.divisor_eq
  · rw [hp.2]
    exact SszNative.Division.step_remainder_lt _ _ _ _ hi.remainder_lt hd (bit_lt _)
  · rw [hp.1]
    exact (quotient_step_bound _ _ _ _ k hk hi.bounded hi.quotient_lt).1
  · rw [hp.1, hp.2, hs]
    exact advance_conservation d _ _ p.1 p.2 n k (source wide s) hk hi.bounded
      hi.conservation (SszNative.Division.step_conservation _ _ _ _)

theorem body_zero (wide : Bool) (s : MachineData) (k : Nat)
    (hc : s.regs.r11.toBitVec.toNat = k) (_hk : 0 < k) (_hb : k ≤ 64) :
    (body wide s).status.zf = decide (k = 1) := by
  cases wide <;> simp only [body, Bool.false_eq_true, ite_false, ite_true,
    wordBody, wideBody, subFlags_zf]
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have he := congrArg BitVec.toNat h
      simp [hc] at he
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp [hc, h]

structure Finished (base : Int64) (wide : Bool) (s : MachineData) (d n : Nat)
    (st : MachineState) : Prop where
  pc : st.2 = endPC base wide
  frame : LoopFrame wide s st.1
  quotient : st.1.regs.rax.toBitVec.toNat = n / d
  remainder_lt : remainder wide st.1 < d
  conservation : st.1.regs.rax.toBitVec.toNat * d + remainder wide st.1 = n

/-- The natural counter is a ranking function for the actual backward branches. -/
theorem loop_runs (base : Int64) (wide : Bool) (d n : Nat) (hd : 0 < d)
    (hn : n < radix * radix) :
    ∀ k (s : MachineData), 0 < k → Invariant wide d n k s →
      Eventually (step base) (Finished base wide s d n) (s, loopPC base wide) := by
  intro k
  refine Nat.strongRecOn k ?_
  intro k ih s hk hi
  have hi' := body_invariant wide s d n k hi hk hn hd
  have hz := body_zero wide s k hi.count hk hi.bounded
  have hnext : Eventually (step base) (Finished base wide s d n)
      (body wide s, if (body wide s).status.zf then endPC base wide else loopPC base wide) := by
    by_cases hone : k = 1
    · have he : (body wide s).regs.rax.toBitVec.toNat * d + remainder wide (body wide s) = n := by
        have h := hi'.conservation
        have hx := (source wide (body wide s)).isLt
        simp [hone] at h
        simpa [Nat.div_eq_of_lt hx] using h
      have hout : Finished base wide s d n (body wide s, endPC base wide) :=
        ⟨rfl, body_frame wide s, quotient_of_conservation _ _ _ _ hd hi'.remainder_lt he,
          hi'.remainder_lt, he⟩
      simpa [hz, hone] using Eventually.done _ hout
    · have hrec := ih (k - 1) (by omega) (body wide s) (by omega) hi'
      have hweaken : ∀ st, Finished base wide (body wide s) d n st → Finished base wide s d n st := by
        intro st hf
        exact ⟨hf.pc, (body_frame wide s).trans hf.frame, hf.quotient,
          hf.remainder_lt, hf.conservation⟩
      simpa [hz, hone] using eventually_weaken _ _ _ _ hweaken hrec
  cases wide
  · exact word_runs base s _ hnext
  · exact wide_runs base s _ hnext

/-- Initial state of either 64-bit pass, possibly carrying a high-limb remainder. -/
theorem word_invariant (s : MachineData) (high : Nat)
    (hq : s.regs.rax.toBitVec = 0) (hc : s.regs.r11.toBitVec = 64)
    (hr : s.regs.r9.toBitVec.toNat = high) (hlt : high < s.regs.rdx.toBitVec.toNat) :
    Invariant false s.regs.rdx.toBitVec.toNat
      (high * radix + s.regs.rsi.toBitVec.toNat) 64 s := by
  constructor <;> simp_all [source, remainder, divisor, radix]

/-- A nonzero high divisor word is greater than every one-word initial remainder. -/
theorem wide_invariant (s : MachineData) (hq : s.regs.rax.toBitVec = 0)
    (hc : s.regs.r11.toBitVec = 64) (hr : s.regs.r10.toBitVec = 0)
    (hd : s.regs.rcx.toBitVec ≠ 0) :
    Invariant true (value s.regs.rdx.toBitVec s.regs.rcx.toBitVec)
      (s.regs.r9.toBitVec.toNat * radix + s.regs.rdi.toBitVec.toNat) 64 s := by
  have hlo := s.regs.r9.toBitVec.isLt
  have hh : 0 < s.regs.rcx.toBitVec.toNat := by
    have hz : s.regs.rcx.toBitVec.toNat ≠ 0 := by
      intro h
      apply hd
      apply BitVec.eq_of_toNat_eq
      simpa using h
    omega
  constructor <;> simp_all [source, remainder, divisor, value, radix] <;> omega

end SszX86.Udivti3
