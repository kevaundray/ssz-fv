import SszX86.ByteViewListOps

namespace SszX86.ByteView.ListCompare
open Kraken.X64.Parser UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

@[simp] theorem register_nat (n : Nat) :
    ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
  apply UInt64.toBitVec_inj.1
  rfl

def nz (s : MachineData) : Nat := if s.regs.r14.toBitVec = 0#64 then 0 else 1

theorem choice (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags) (b : Bool)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      (listState s a c (if b then 1#64 else 0#64) x y fl,
        if b then base + 2591 else base + 2759)) :
    Eventually (step e) P
      (listState s a c (if b then 1#64 else 0#64) x y fl, base + 2519) := by
  have reject := hc.targets ("u2591", 2591) (by decide)
  cases b
  · view_list_step 99 using hc
    constructor <;> view_list_step 100 using hc
    all_goals simp [StatusFlags.from_result, Effects.All]
    all_goals view_list_step 101 using hc
    all_goals simpa [listState] using hp _
  · view_list_step 99 using hc
    constructor <;> view_list_step 100 using hc
    all_goals simpa [reject, StatusFlags.from_result, listState, Effects.All] using hp _

theorem count_nonzero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x : BitVec 64) (fl : StatusFlags) (n : Nat)
    (hn : 0 < n) (hb : n < 2^64)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (listState s a c si x y fl,
        if n = nz s then base + 902 else base + 2759)) :
    Eventually (step e) P
      (listState s a c (BitVec.ofNat 64 (nz s)) x (BitVec.ofNat 64 n) fl, base + 889) := by
  have target := hc.targets ("u2519", 2519) (by decide)
  view_list_step 41 using hc
  view_list_step 42 using hc
  view_list_step 43 using hc
  by_cases hz : s.regs.r14.toBitVec = 0#64
  · have hnz : BitVec.ofNat 64 n ≠ 0#64 := by bv_omega
    simp [nz, hz, StatusFlags.from_result, Nat.mod_eq_of_lt hb, hnz, target, Effects.All]
    apply choice e base hc _ _ _ _ _ _ false
    intro fl'
    simpa [nz, hz, Nat.ne_of_gt hn, listState] using hp 0#64 x (BitVec.ofNat 64 n) fl'
  · by_cases he : n = 1
    · subst n
      simpa [nz, hz, StatusFlags.from_result, listState, Effects.All] using hp 0#64 x 1#64 _
    · have hnz : BitVec.ofNat 64 n ≠ 1#64 := by bv_omega
      have hnot : ¬ n < 1 := by omega
      simp [nz, hz, StatusFlags.from_result, Nat.mod_eq_of_lt hb, hnz, hnot, target, Effects.All]
      apply choice e base hc _ _ _ _ _ _ false
      intro fl'
      simpa [nz, hz, he, listState] using hp 0#64 x (BitVec.ofNat 64 n) fl'

theorem count_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (listState s a c si x y fl,
        if s.regs.r14.toBitVec = 0#64 then base + 902 else base + 2591)) :
    Eventually (step e) P
      (listState s a c (BitVec.ofNat 64 (nz s)) x y fl, base + 2503) := by
  have target := hc.targets ("u902", 902) (by decide)
  have zeroSet : (0#56 ++ BitVec.ofNat 8 ((0#64).unsigned != 0).toNat) = 0#64 := by decide
  view_list_step 95 using hc
  constructor <;> view_list_step 96 using hc
  all_goals view_list_step 97 using hc
  all_goals view_list_step 98 using hc
  all_goals
    by_cases hz : s.regs.r14.toBitVec = 0#64
    · simpa [nz, hz, target, StatusFlags.from_result, zeroSet, listState, Effects.All]
        using hp 0#64 x 0#64 _
    · simp [nz, hz, StatusFlags.from_result, Effects.All]
      apply choice e base hc _ _ _ _ _ _ true
      intro fl'
      simpa [hz, listState] using hp 1#64 x 0#64 fl'

theorem equal_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a : BitVec 64) (words : List (BitVec 64))
    (si x y : BitVec 64) (fl : StatusFlags)
    (hb : words.length < 2^64)
    (he : sigWords words = nz s)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (listState s a (BitVec.ofNat 64 words.length) si x y fl,
        if s.regs.r14.toNat ≤ value words then base + 2759 else base + 2591)) :
    Eventually (step e) P
      (listState s a (BitVec.ofNat 64 words.length) si x y fl, base + 902) := by
  have target := hc.targets ("u2759", 2759) (by decide)
  have reject := hc.targets ("u2591", 2591) (by decide)
  have scalarTarget := hc.targets ("u2582", 2582) (by decide)
  view_list_step 44 using hc
  constructor <;> view_list_step 45 using hc
  all_goals
    by_cases hz : s.regs.r14.toBitVec = 0#64
    · have hzero : s.regs.r14.toNat = 0 := by simpa using congrArg BitVec.toNat hz
      simpa [target, StatusFlags.from_result, hz, hzero, listState, Effects.All] using hp _ _ _ _
    · simp [StatusFlags.from_result, hz, Effects.All]
      have hs : sigWords words = 1 := by simpa [nz, hz] using he
      have hpos : 0 < words.length := by have := sigWords_le_length words; omega
      have hc0 : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      have hv : value words = (words[0]?.getD 0#64).toNat := by
        rw [← trim_value words, trim_eq_take, hs]
        cases words <;> simp [value]
      view_list_step 46 using hc
      constructor <;> view_list_step 47 using hc
      all_goals simp [StatusFlags.from_result, hc0, Effects.All]
      all_goals view_list_step 48 using hc
      all_goals
        have hload : Mem.loadInt s.dmem a 8 = some ((words[0]?.getD 0#64).toNat : Int) := by
          simpa [List.getElem?_eq_getElem hpos] using hm ⟨0, hpos⟩
        view_vector_load hload
        view_list_step 49 using hc
        view_list_step 50 using hc
        by_cases heq : s.regs.r14.toBitVec = words[0]?.getD 0#64
        · simp [StatusFlags.from_result, heq, Effects.All]
          view_list_step 51 using hc
          have hle : s.regs.r14.toNat ≤ value words := by
            rw [hv, ← heq]
            exact Nat.le_refl _
          simpa [hle, listState] using hp _ _ _ _
        · simp [scalarTarget, StatusFlags.from_result, heq, Effects.All]
          apply scalar e base hc
          intro fl'
          simpa [hv, listState] using hp _ _ _ fl'

theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si y limb : BitVec 64) (fl : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      (listState s a c si (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) fl,
        if limb = 0#64 then base + 864 else base + 889)) :
    Eventually (step e) P
      (listState s a c si (BitVec.ofNat 64 (n+2)) y fl, base + 864) := by
  have target := hc.targets ("u864", 864) (by decide)
  have hz : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hpred : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by
    bv_omega
  have haddr : BitVec.ofInt 64 (a.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      a + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  view_list_step 35 using hc
  view_list_step 36 using hc
  simp [StatusFlags.from_result, hz, Effects.All]
  view_list_step 37 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hpred]
  view_list_step 38 using hc
  rw [haddr]
  view_vector_load hm
  view_list_step 39 using hc
  view_list_step 40 using hc
  by_cases h : limb = 0#64
  · simpa [target, StatusFlags.from_result, h, listState, Effects.All] using hp _
  · simpa [StatusFlags.from_result, h, listState, Effects.All] using hp _

theorem scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ y fl,
    (significantCount words n = 0 → ∀ x y fl,
      Eventually (step e) P (listState s a c si x y fl, base + 2503)) →
    (∀ k, significantCount words n = k → 0 < k → ∀ x fl,
      Eventually (step e) P (listState s a c si x (BitVec.ofNat 64 k) fl, base + 889)) →
    Eventually (step e) P
      (listState s a c si (BitVec.ofNat 64 (n+1)) y fl, base + 864) := by
  intro n
  induction n with
  | zero =>
    intro hn y fl hzero hpos
    have target := hc.targets ("u2503", 2503) (by decide)
    view_list_step 35 using hc
    view_list_step 36 using hc
    simpa [target, StatusFlags.from_result, listState, Effects.All] using hzero rfl 1#64 y _
  | succ n ih =>
    intro hn y fl hzero hpos
    have hload := hm ⟨n, by omega⟩
    have hload' : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hload
    apply scan_step e base hc s a c si y (words[n]?.getD 0#64) fl n (by omega) hload' P
    intro fl'
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · simp only [hz, ↓reduceIte]
      apply ih (by omega) _ fl'
      · intro he
        apply hzero
        simpa [significantCount, hz] using he
      · intro k he hk
        apply hpos k
        · simpa [significantCount, hz] using he
        · exact hk
    · simp only [hz, ↓reduceIte]
      exact hpos (n+1) (by simp [significantCount, hz]) (by omega) _ fl'

theorem value_zero (words : List (BitVec 64)) (h : sigWords words = 0) :
    value words = 0 := by
  rw [← trim_value words, trim_eq_take, h]
  rfl

theorem value_many (s : MachineData) (words : List (BitVec 64)) (h : 1 < sigWords words) :
    s.regs.r14.toNat ≤ value words := by
  have hh := canonical_length_lt (xs := [s.regs.r14.toBitVec])
    (trim_canonical words) (by simpa only [List.length_cons, List.length_nil, trim_length] using h)
  simp only [value, Nat.mul_zero, Nat.add_zero, trim_value] at hh
  exact Nat.le_of_lt hh

theorem large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a y : BitVec 64) (fl : StatusFlags) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (listState s a (BitVec.ofNat 64 words.length) si x y fl,
        if s.regs.r14.toNat ≤ value words then base + 2759 else base + 2591)) :
    Eventually (step e) P
      (listState s a (BitVec.ofNat 64 words.length) (BitVec.ofNat 64 (nz s))
        (BitVec.ofNat 64 (words.length+1)) y fl, base + 864) := by
  apply scan e base hc s a (BitVec.ofNat 64 words.length) (BitVec.ofNat 64 (nz s))
    words hb hm P words.length (Nat.le_refl _) y fl
  · intro hz x y fl'
    change sigWords words = 0 at hz
    have hv := value_zero words hz
    apply count_zero e base hc
    intro si x y fl''
    by_cases hs : s.regs.r14.toBitVec = 0#64
    · simp only [hs, ↓reduceIte]
      apply equal_count e base hc s a words si x y fl'' (by omega)
        (by simpa [nz, hs] using hz) hm P hp
    · have hpos : 0 < s.regs.r14.toNat := by
        have hne : s.regs.r14.toNat ≠ 0 := by
          intro he
          exact hs (BitVec.eq_of_toNat_eq he)
        omega
      simpa only [hs, ↓reduceIte, hv, Nat.not_le_of_gt hpos] using hp si x y fl''
  · intro k hk hpos x fl'
    change sigWords words = k at hk
    have hkle : k ≤ words.length := by rw [← hk]; exact sigWords_le_length words
    apply count_nonzero e base hc s a (BitVec.ofNat 64 words.length) x fl' k hpos (by omega)
    intro si x y fl''
    by_cases he : k = nz s
    · simp only [he, ↓reduceIte]
      exact equal_count e base hc s a words si x y fl'' (by omega) (hk.trans he) hm P hp
    · have hle : s.regs.r14.toNat ≤ value words := by
        by_cases hs : s.regs.r14.toBitVec = 0#64
        · have hzero : s.regs.r14.toNat = 0 := by simpa using congrArg BitVec.toNat hs
          simp [hzero]
        · have hk1 : k ≠ 1 := by simpa [nz, hs] using he
          apply value_many s words
          omega
      simpa only [he, ↓reduceIte, hle] using hp si x y fl''

theorem header (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c : BitVec 64) (P : MachineState → Prop)
    (ha : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (a.toNat : Int))
    (hn : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (c.toNat : Int))
    (hsmall : a = 0#64 → ∀ x y fl,
      Eventually (step e) P (listState s a c 0#64 x y fl, base + 2422))
    (hlarge : a ≠ 0#64 → ∀ y fl,
      Eventually (step e) P
        (listState s a c (BitVec.ofNat 64 (nz s)) (c + 1#64) y fl, base + 864)) :
    Eventually (step e) P (s, base + 824) := by
  have target := hc.targets ("u2422", 2422) (by decide)
  view_list_step 25 using hc
  view_vector_load ha
  view_list_step 26 using hc
  view_vector_load hn
  view_list_step 27 using hc
  constructor <;> view_list_step 28 using hc
  all_goals constructor <;> view_list_step 29 using hc
  all_goals view_list_step 30 using hc
  all_goals constructor <;> view_list_step 31 using hc
  all_goals
    by_cases hz : a = 0#64
    · simpa [target, StatusFlags.from_result, hz, listState, Effects.All] using hsmall hz _ _ _
    · simp [StatusFlags.from_result, hz, Effects.All]
      view_list_step 32 using hc
      view_list_step 33 using hc
      view_list_step 34 using hc
      by_cases hs : s.regs.r14.toBitVec = 0#64
      · simpa [nz, hs, StatusFlags.from_result, BitVec.ofInt_add, BitVec.ofInt_toInt, listState]
          using hlarge hz _ _
      · simpa [nz, hs, StatusFlags.from_result, BitVec.ofInt_add, BitVec.ofInt_toInt, listState]
          using hlarge hz _ _

def Post (s : MachineData) (base : Int64) (limit : Nat) (t : MachineState) : Prop :=
  Frame s t.1 ∧
  t.2 = (if s.regs.r14.toNat ≤ limit then base + 2759 else base + 2591) ∧
  Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (t.1.regs.rax.toNat : Int) ∧
  Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (t.1.regs.rcx.toNat : Int)

theorem runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limit : Nat)
    (hwidth : SszNative.NatMemory.At (widthLoad s.dmem) (s.regs.rbp.toNat + 8) limit) :
    Eventually (step e) (Post s base limit) (s, base + 824) := by
  have addr (n : Nat) : BitVec.ofNat 64 (s.regs.rbp.toNat + n) =
      s.regs.rbp.toBitVec + BitVec.ofNat 64 n := width_address _ _
  rcases hwidth with ⟨⟨ha, hc'⟩, hv⟩ | ⟨pointer, words, hlarge, hvalue⟩
  · have ha' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (0 : Int) := by
      simpa [addr] using widthLoad_eq s.dmem _ 8 0 ha
    have hc'' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (limit : Int) := by
      simpa only [Nat.add_assoc, addr] using widthLoad_eq s.dmem _ 8 limit hc'
    have hn : (BitVec.ofNat 64 limit).toNat = limit := Nat.mod_eq_of_lt hv
    apply header e base hc s 0#64 (BitVec.ofNat 64 limit) (Post s base limit) ha'
    · simpa only [hn] using hc''
    · intro _ x y fl
      apply small e base hc
      intro si x y fl'
      apply Eventually.done
      exact ⟨state_frame _ _ _ _ _ _ _, by simp only [hn], ha',
        by simpa only [listState, UInt64.toNat_ofBitVec, hn] using hc''⟩
    · intro he
      exact (he rfl).elim
  · rcases hlarge with ⟨hptr, hptrBound, _halign, hrange, ha, hc', hwords⟩
    have hlen : words.length + 1 < 2^64 := by omega
    let a := BitVec.ofNat 64 pointer
    let c := BitVec.ofNat 64 words.length
    have han : a.toNat = pointer := Nat.mod_eq_of_lt hptrBound
    have hcn : c.toNat = words.length := Nat.mod_eq_of_lt (by omega)
    have ha' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (a.toNat : Int) := by
      simpa only [addr, han] using widthLoad_eq s.dmem _ 8 pointer ha
    have hc'' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (c.toNat : Int) := by
      simpa only [Nat.add_assoc, addr, hcn] using widthLoad_eq s.dmem _ 8 words.length hc'
    have ha0 : a ≠ 0#64 := by
      intro he
      have := congrArg BitVec.toNat he
      rw [han] at this
      simp only [BitVec.toNat_ofNat] at this
      omega
    have loads (i : Fin words.length) :
        Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int) := by
      have h := widthLoad_eq s.dmem _ 8 _ (hwords i)
      simpa only [← han, width_address] using h
    apply header e base hc s a c (Post s base limit) ha' hc''
    · intro he
      exact (ha0 he).elim
    · intro _ y fl
      have hinc : c + 1#64 = BitVec.ofNat 64 (words.length+1) := by
        dsimp only [c]
        rw [BitVec.ofNat_add]
      rw [hinc]
      apply large e base hc s a y fl words hlen loads
      intro si x y fl'
      apply Eventually.done
      exact ⟨state_frame _ _ _ _ _ _ _, by simp only [hvalue], ha', hc''⟩

end SszX86.ByteView.ListCompare
