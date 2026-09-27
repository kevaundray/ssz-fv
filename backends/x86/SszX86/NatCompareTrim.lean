import SszX86.NatCompareExec

namespace SszX86.NatCompare
open SszNative.Limbs
open UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- A borrowed operand's concrete limb observations. Small operands use one
logical limb, including zero; Large operands retain every stored high zero. -/
def View (m : DataMem) (pointer payload : BitVec 64) (words : List (BitVec 64)) : Prop :=
  (pointer = 0#64 ∧ words = [payload]) ∨
  (pointer ≠ 0#64 ∧ payload = BitVec.ofNat 64 words.length ∧
    words.length + 1 < 2^64 ∧
    ∀ i : Fin words.length,
      Mem.loadInt m (pointer + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))

theorem pair_view (m : DataMem) (pointer payload : BitVec 64) (value : Nat)
    (h : SszNative.NatMemory.Pair (widthLoad m) pointer payload value) :
    ∃ words, View m pointer payload words ∧ SszNative.Limbs.value words = value := by
  rcases h with ⟨hz, hv⟩ | ⟨words, hpos, halign, hspace, hcount, hm, hv⟩
  · exact ⟨[payload], Or.inl ⟨hz, rfl⟩, by simpa [SszNative.Limbs.value] using hv⟩
  · refine ⟨words, Or.inr ⟨?_, ?_, ?_, ?_⟩, hv⟩
    · intro hz
      simp [hz] at hpos
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← hcount, Nat.mod_eq_of_lt payload.isLt]
    · omega
    · intro i
      simpa only [width_address] using widthLoad_eq m _ _ _ (hm i)

theorem view_bound {m : DataMem} {p c : BitVec 64} {ws : List (BitVec 64)}
    (h : View m p c ws) : ws.length + 1 < 2^64 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, hb, _⟩
  · simp
  · exact hb

theorem single_sig (v : BitVec 64) : sigWords [v] = if v = 0#64 then 0 else 1 := by
  simp [sigWords, significantCount]

def rightEntry (s : MachineData) (base : Int64) : Int64 :=
  if s.regs.rdx.toBitVec = 0#64 then base + 95 else base + 54

/-- Both predecessor blocks implement the same pointer dispatch for the RHS. -/
theorem right_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (state s a d x y flags, rightEntry s base)) :
    Eventually (step e) P (state s a d x y flags, base + 49) ∧
    Eventually (step e) P (state s a d x y flags, base + 90) := by
  have target95 := hc.targets ("natCompare_u95", 95) (by decide)
  have target54 := hc.targets ("natCompare_u54", 54) (by decide)
  constructor
  · natcmp_step 14 using hc
    constructor <;> natcmp_step 15 using hc
    all_goals
      by_cases hz : s.regs.rdx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, target95, hz, rightEntry, state, Effects.All] using hp _
      · simpa [StatusFlags.from_result, hz, rightEntry, state, Effects.All] using hp _
  · natcmp_step 26 using hc
    constructor <;> natcmp_step 27 using hc
    all_goals
      by_cases hz : s.regs.rdx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, hz, rightEntry, state, Effects.All] using hp _
      · simpa [StatusFlags.from_result, target54, hz, rightEntry, state, Effects.All] using hp _

/-- One actual left countdown iteration, reading exactly the indexed limb. -/
theorem left_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d x y limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hz : limb = 0#64 → ∀ flags, Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+1)) d (BitVec.ofNat 64 (n+1)) y flags, base + 16))
    (hn : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+1)) d (BitVec.ofNat 64 (n+1)) y flags, base + 49)) :
    Eventually (step e) P (state s (BitVec.ofNat 64 (n+2)) d x y flags, base + 16) := by
  have target := hc.targets ("natCompare_u16", 16) (by decide)
  have hne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hdec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have haddr : BitVec.ofInt 64 (d.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      d + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  natcmp_step 4 using hc
  natcmp_step 5 using hc
  simp [StatusFlags.from_result, hne, Effects.All]
  natcmp_step 6 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hdec]
  natcmp_step 7 using hc
  rw [haddr]
  natcmp_load hm
  natcmp_step 8 using hc
  natcmp_step 9 using hc
  by_cases hl : limb = 0#64
  · simpa [StatusFlags.from_result, hl, target, state, Effects.All] using hz hl _
  · simp [StatusFlags.from_result, hl, Effects.All]
    natcmp_step 10 using hc
    simpa [state] using hn hl _

theorem left_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d y : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ x flags,
    (∀ a flags, Eventually (step e) P
      (state s a d (BitVec.ofNat 64 (significantCount words n)) y flags, rightEntry s base)) →
    Eventually (step e) P (state s (BitVec.ofNat 64 (n+1)) d x y flags, base + 16) := by
  intro n
  induction n with
  | zero =>
    intro hn x flags hp
    have target := hc.targets ("natCompare_u87", 87) (by decide)
    natcmp_step 4 using hc
    natcmp_step 5 using hc
    simp [StatusFlags.from_result, target, Effects.All]
    natcmp_step 25 using hc
    constructor <;> apply (right_dispatch e base hc s _ d 0 y _ P _).2
    all_goals intro fl; simpa [significantCount, state] using hp 1#64 fl
  | succ n ih =>
    intro hn x flags hp
    have hload : Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply left_scan_step e base hc s d x y _ flags n (by omega) hload P
    · intro hz fl
      apply ih (by omega) _ fl
      intro a fl
      simpa [significantCount, hz] using hp a fl
    · intro hn fl
      apply (right_dispatch e base hc s _ d _ y fl P _).1
      intro fl
      simpa [significantCount, hn] using hp (BitVec.ofNat 64 (n+1)) fl

/-- One actual right countdown iteration; its pointer and count stay unchanged. -/
theorem right_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d x y limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hz : limb = 0#64 → ∀ flags, Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+1)) d x (BitVec.ofNat 64 (n+1)) flags, base + 64))
    (hn : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+1)) d x (BitVec.ofNat 64 (n+1)) flags, base + 110)) :
    Eventually (step e) P (state s (BitVec.ofNat 64 (n+2)) d x y flags, base + 64) := by
  have target := hc.targets ("natCompare_u64", 64) (by decide)
  have hne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hdec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have haddr : BitVec.ofInt 64 (s.regs.rdx.toBitVec.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  natcmp_step 18 using hc
  natcmp_step 19 using hc
  simp [StatusFlags.from_result, hne, Effects.All]
  natcmp_step 20 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hdec]
  natcmp_step 21 using hc
  rw [haddr]
  natcmp_load hm
  natcmp_step 22 using hc
  natcmp_step 23 using hc
  by_cases hl : limb = 0#64
  · simpa [StatusFlags.from_result, hl, target, state, Effects.All] using hz hl _
  · simp [StatusFlags.from_result, hl, Effects.All]
    natcmp_step 24 using hc
    simpa [state] using hn hl _

theorem right_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d x : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ y flags,
    (∀ a flags, Eventually (step e) P
      (state s a d x (BitVec.ofNat 64 (significantCount words n)) flags, base + 110)) →
    Eventually (step e) P (state s (BitVec.ofNat 64 (n+1)) d x y flags, base + 64) := by
  intro n
  induction n with
  | zero =>
    intro hn y flags hp
    have target := hc.targets ("natCompare_u107", 107) (by decide)
    natcmp_step 18 using hc
    natcmp_step 19 using hc
    simp [StatusFlags.from_result, target, Effects.All]
    natcmp_step 32 using hc
    constructor <;> simpa [significantCount, state] using hp 1#64 _
  | succ n ih =>
    intro hn y flags hp
    have hload : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply right_scan_step e base hc s d x y _ flags n (by omega) hload P
    · intro hz fl
      apply ih (by omega) _ fl
      intro a fl
      simpa [significantCount, hz] using hp a fl
    · intro hn fl
      simpa [significantCount, hn] using hp (BitVec.ofNat 64 (n+1)) fl

theorem left_words (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hv : View s.dmem d s.regs.rsi.toBitVec words)
    (P : MachineState → Prop)
    (hp : ∀ a flags, Eventually (step e) P
      (state s a d (BitVec.ofNat 64 (sigWords words)) y flags, rightEntry s base)) :
    Eventually (step e) P (state s a d x y flags, base + 0) := by
  have target := hc.targets ("natCompare_u39", 39) (by decide)
  rcases hv with ⟨rfl, rfl⟩ | ⟨hn, hcount, hb, hm⟩
  · natcmp_step 0 using hc
    constructor <;> natcmp_step 1 using hc
    all_goals simp [StatusFlags.from_result, target, Effects.All]
    all_goals natcmp_step 11 using hc
    all_goals constructor <;> natcmp_step 12 using hc
    all_goals constructor <;> natcmp_step 13 using hc
    all_goals
      by_cases hz : s.regs.rsi.toBitVec = 0#64
      · simp [StatusFlags.from_result, hz]
        apply (right_dispatch e base hc s a 0 0 y _ P _).1
        intro fl
        simpa [single_sig, hz] using hp a fl
      · have ht : (s.regs.rsi.toBitVec == 0#64) = false := beq_eq_false_iff_ne.mpr hz
        simp [StatusFlags.from_result, ht]
        apply (right_dispatch e base hc s a 0 1 y _ P _).1
        intro fl
        simpa [single_sig, hz] using hp a fl
  · have hplus : s.regs.rsi + 1 = UInt64.ofBitVec (BitVec.ofNat 64 (words.length+1)) := by
      apply UInt64.toBitVec_inj.1
      change s.regs.rsi.toBitVec + 1#64 = _
      rw [hcount]
      bv_omega
    natcmp_step 0 using hc
    constructor <;> natcmp_step 1 using hc
    all_goals simp [StatusFlags.from_result, hn, Effects.All]
    all_goals natcmp_step 2 using hc
    all_goals simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    all_goals natcmp_step 3 using hc
    all_goals rw [hplus]
    all_goals
      apply left_scan e base hc s d y words hb hm P words.length (Nat.le_refl _) x _
      exact hp

theorem right_words (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64))
    (hv : View s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec words)
    (P : MachineState → Prop)
    (hp : ∀ a flags, Eventually (step e) P
      (state s a d x (BitVec.ofNat 64 (sigWords words)) flags, base + 110)) :
    Eventually (step e) P (state s a d x y flags, rightEntry s base) := by
  rcases hv with ⟨hz, rfl⟩ | ⟨hn, hcount, hb, hm⟩
  · simp only [rightEntry, hz, ↓reduceIte]
    natcmp_step 28 using hc
    constructor <;> natcmp_step 29 using hc
    all_goals constructor <;> natcmp_step 30 using hc
    all_goals natcmp_step 31 using hc
    all_goals
      by_cases hz : s.regs.rcx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, single_sig, hz, state] using hp a _
      · have ht : (s.regs.rcx.toBitVec == 0#64) = false := beq_eq_false_iff_ne.mpr hz
        simpa [StatusFlags.from_result, single_sig, hz, ht, state] using hp a _
  · simp only [rightEntry, hn, ↓reduceIte]
    have hplus : s.regs.rcx + 1 = UInt64.ofBitVec (BitVec.ofNat 64 (words.length+1)) := by
      apply UInt64.toBitVec_inj.1
      change s.regs.rcx.toBitVec + 1#64 = _
      rw [hcount]
      bv_omega
    natcmp_step 16 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    natcmp_step 17 using hc
    rw [hplus]
    apply right_scan e base hc s d x words hb hm P words.length (Nat.le_refl _) y _
    exact hp

/-- Entry through both length normalizations; neither operand is canonicalized
in memory, and either or both may be a zero-length Large value. -/
theorem trim_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (xs ys : List (BitVec 64))
    (hx : View s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec xs)
    (hy : View s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec ys)
    (P : MachineState → Prop)
    (hp : ∀ a flags, Eventually (step e) P
      (state s a s.regs.rdi.toBitVec (BitVec.ofNat 64 (sigWords xs))
        (BitVec.ofNat 64 (sigWords ys)) flags, base + 110)) :
    Eventually (step e) P (s, base) := by
  have h := left_words e base hc s s.regs.rax.toBitVec s.regs.rdi.toBitVec
    s.regs.r8.toBitVec s.regs.r9.toBitVec s.status xs hx P
    (fun a flags => right_words e base hc s a s.regs.rdi.toBitVec
      (BitVec.ofNat 64 (sigWords xs)) s.regs.r9.toBitVec flags ys hy P hp)
  simpa only [state_initial, Int64.add_zero] using h

end SszX86.NatCompare
