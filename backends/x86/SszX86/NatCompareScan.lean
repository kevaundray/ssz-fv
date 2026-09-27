import SszX86.NatCompareTrim

namespace SszX86.NatCompare
open SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- Continuations at both real RET instructions. Register high bits and flags
are deliberately not observations of the Nat comparison ABI. -/
def Exits (e : Executable) (base : Int64) (s : MachineData)
    (P : MachineState → Prop) (ord : Ordering) : Prop :=
  ∀ a d x y flags, a.setWidth 8 = orderingByte ord →
    Eventually (step e) P (state s a d x y flags, base + 234) ∧
    Eventually (step e) P (state s a d x y flags, base + 372)

theorem scan_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop) (hp : Exits e base s P .eq) :
    Eventually (step e) P (state s a d x y flags, base + 370) := by
  apply zero_runs e base hc
  intro fl
  exact (hp 0 d x y fl rfl).2

theorem scan_unequal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop) (hp : Exits e base s P (compare a.toNat y.toNat)) :
    Eventually (step e) P (state s a d x y flags, base + 226) := by
  apply encode_runs e base hc
  intro a' fl he
  exact (hp a' d x y fl he).1

/-- The Large/Large loop reads only indices below both original slice lengths.
Consequently the zero-extension fallback blocks are unreachable on this path. -/
theorem large_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d y lhs rhs : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n < 2^64 - 1)
    (hx : n < s.regs.rsi.toNat) (hy : n < s.regs.rcx.toNat)
    (hl : Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*n)) 8 = some (lhs.toNat : Int))
    (hr : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n)) 8 = some (rhs.toNat : Int))
    (P : MachineState → Prop)
    (heq : lhs = rhs → ∀ flags, Eventually (step e) P
      (state s lhs d (BitVec.ofNat 64 n - 1) rhs flags, base + 172))
    (hne : lhs ≠ rhs → ∀ flags, Eventually (step e) P
      (state s lhs d (BitVec.ofNat 64 n - 1) rhs flags, base + 226)) :
    Eventually (step e) P (state s a d (BitVec.ofNat 64 n) y flags, base + 172) := by
  have target160 := hc.targets ("natCompare_u160", 160) (by decide)
  have target226 := hc.targets ("natCompare_u226", 226) (by decide)
  have hn : BitVec.ofNat 64 n ≠ 18446744073709551615#64 := by bv_omega
  have haddr (p : BitVec 64) :
      BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 n).toInt * 8) =
        p + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide]
    bv_omega
  natcmp_step 48 using hc
  natcmp_step 49 using hc
  simp [StatusFlags.from_result, hn, Effects.All]
  natcmp_step 50 using hc
  natcmp_step 51 using hc
  simp [StatusFlags.from_result, Nat.mod_eq_of_lt (show n < 2^64 by omega),
    Nat.not_le_of_gt hx, Effects.All]
  natcmp_step 52 using hc
  rw [haddr]
  natcmp_load hl
  natcmp_step 53 using hc
  natcmp_step 54 using hc
  simp [StatusFlags.from_result, Nat.mod_eq_of_lt (show n < 2^64 by omega),
    hy, target160, Effects.All]
  natcmp_step 44 using hc
  rw [haddr]
  natcmp_load hr
  natcmp_step 45 using hc
  natcmp_step 46 using hc
  natcmp_step 47 using hc
  by_cases he : lhs = rhs
  · simpa [StatusFlags.from_result, he, state, Effects.All] using heq he _
  · simpa [StatusFlags.from_result, he, target226, state, Effects.All] using hne he _

theorem large_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d : BitVec 64) (xs ys : List (BitVec 64))
    (hxc : s.regs.rsi.toBitVec = BitVec.ofNat 64 xs.length)
    (hyc : s.regs.rcx.toBitVec = BitVec.ofNat 64 ys.length)
    (hxb : xs.length + 1 < 2^64) (hyb : ys.length + 1 < 2^64)
    (hxm : ∀ i : Fin xs.length,
      Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*i.val)) 8 = some (xs[i].toNat : Int))
    (hym : ∀ i : Fin ys.length,
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 = some (ys[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ xs.length → n ≤ ys.length → ∀ a y flags,
    Exits e base s P (scanDesc xs ys n) →
    Eventually (step e) P (state s a d (BitVec.ofNat 64 n - 1) y flags, base + 172) := by
  intro n
  induction n with
  | zero =>
    intro hx hy a y flags hp
    have target := hc.targets ("natCompare_u370", 370) (by decide)
    natcmp_step 48 using hc
    natcmp_step 49 using hc
    simp [StatusFlags.from_result, target, Effects.All]
    exact scan_zero e base hc s a d _ y _ P hp
  | succ n ih =>
    intro hx hy a y flags hp
    have hxl : n < xs.length := by omega
    have hyl : n < ys.length := by omega
    have hloadx : Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*n)) 8 =
        some ((xs[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem hxl] using hxm ⟨n, hxl⟩
    have hloady : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((ys[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem hyl] using hym ⟨n, hyl⟩
    have hcx : n < s.regs.rsi.toNat := by
      change n < s.regs.rsi.toBitVec.toNat
      rw [hxc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : xs.length < 2^64)]
      exact hxl
    have hcy : n < s.regs.rcx.toNat := by
      change n < s.regs.rcx.toBitVec.toNat
      rw [hyc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ys.length < 2^64)]
      exact hyl
    rw [show BitVec.ofNat 64 (n+1) - 1 = BitVec.ofNat 64 n by bv_omega]
    apply large_scan_step e base hc s a d y _ _ flags n (by omega) hcx hcy hloadx hloady P
    · intro he fl
      apply ih (by omega) (by omega) _ _ fl
      simpa [scanDesc, he] using hp
    · intro he fl
      apply scan_unequal e base hc
      have hn : (xs[n]?.getD 0#64).toNat ≠ (ys[n]?.getD 0#64).toNat := by
        intro hh
        exact he (BitVec.eq_of_toNat_eq hh)
      have hcmp : compare (xs[n]?.getD 0#64).toNat (ys[n]?.getD 0#64).toNat ≠ .eq := by
        intro hh
        exact hn (Nat.compare_eq_eq.mp hh)
      cases hh : compare (xs[n]?.getD 0).toNat (ys[n]?.getD 0).toNat with
      | eq => exact False.elim (hcmp hh)
      | lt => simpa only [scanDesc, hh] using hp
      | gt => simpa only [scanDesc, hh] using hp

theorem scanDesc_one (xs ys : List (BitVec 64)) :
    scanDesc xs ys 1 = compare (xs[0]?.getD 0#64).toNat (ys[0]?.getD 0#64).toNat := by
  unfold scanDesc
  cases compare (xs[0]?.getD 0#64).toNat (ys[0]?.getD 0#64).toNat <;> rfl

theorem mixed_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop) (hp : Exits e base s P .eq) :
    Eventually (step e) P (state s a d 18446744073709551615#64 y flags, base + 263) ∧
    Eventually (step e) P (state s a d 18446744073709551615#64 y flags, base + 296) := by
  have target := hc.targets ("natCompare_u370", 370) (by decide)
  constructor
  · natcmp_step 73 using hc
    natcmp_step 74 using hc
    simp [StatusFlags.from_result, target, Effects.All]
    exact scan_zero e base hc s a d _ y _ P hp
  · natcmp_step 86 using hc
    natcmp_step 87 using hc
    simp [StatusFlags.from_result, target, Effects.All]
    exact scan_zero e base hc s a d _ y _ P hp

/-- The mixed path can scan at most one limb, because the Small side has at
most one significant limb. The Large side may still have arbitrary high zeros. -/
theorem large_small_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d : BitVec 64) (xs : List (BitVec 64))
    (hxc : s.regs.rsi.toBitVec = BitVec.ofNat 64 xs.length)
    (hxb : xs.length + 1 < 2^64)
    (hxm : ∀ i : Fin xs.length,
      Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*i.val)) 8 = some (xs[i].toNat : Int))
    (n : Nat) (hn : n ≤ 1) (hx : n ≤ xs.length)
    (a y : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (hp : Exits e base s P (scanDesc xs [s.regs.rcx.toBitVec] n)) :
    Eventually (step e) P (state s a d (BitVec.ofNat 64 n - 1) y flags, base + 263) := by
  cases n with
  | zero => exact (mixed_zero e base hc s a d y flags P hp).1
  | succ n =>
    have hn0 : n = 0 := by omega
    subst n
    have hcpos : 0 < s.regs.rsi.toBitVec.toNat := by
      rw [hxc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : xs.length < 2^64)]
      omega
    have hcarry : (-s.regs.rsi.toBitVec).unsigned ≠
        (0#64).unsigned - s.regs.rsi.toBitVec.unsigned := by
      simp only [BitVec.unsigned, BitVec.toNat_zero]
      omega
    have hload : Mem.loadInt s.dmem d 8 = some ((xs[0]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show 0 < xs.length by omega)] using hxm ⟨0, by omega⟩
    have target240 := hc.targets ("natCompare_u240", 240) (by decide)
    have target226 := hc.targets ("natCompare_u226", 226) (by decide)
    have hp' : Exits e base s P (compare (xs[0]?.getD 0#64).toNat s.regs.rcx.toBitVec.toNat) := by
      simpa [scanDesc_one] using hp
    natcmp_step 73 using hc
    natcmp_step 74 using hc
    simp [StatusFlags.from_result, Effects.All]
    natcmp_step 75 using hc
    natcmp_step 76 using hc
    simp [StatusFlags.from_result, hcarry, target240, Effects.All]
    natcmp_step 67 using hc
    natcmp_load hload
    natcmp_step 68 using hc
    natcmp_step 69 using hc
    natcmp_step 70 using hc
    simp [StatusFlags.from_result, BitVec.unsigned]
    natcmp_step 71 using hc
    natcmp_step 72 using hc
    by_cases he : xs[0]?.getD 0#64 = s.regs.rcx.toBitVec
    · simp [StatusFlags.from_result, he, Effects.All]
      apply (mixed_zero e base hc s _ d _ _ P _).1
      simpa [he] using hp'
    · simp [StatusFlags.from_result, he, target226, Effects.All]
      exact scan_unequal e base hc s _ d _ _ _ P hp'

theorem small_large_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ys : List (BitVec 64))
    (hyc : s.regs.rcx.toBitVec = BitVec.ofNat 64 ys.length)
    (hyb : ys.length + 1 < 2^64)
    (hym : ∀ i : Fin ys.length,
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (ys[i].toNat : Int))
    (n : Nat) (hn : n ≤ 1) (hy : n ≤ ys.length)
    (a d y : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (hp : Exits e base s P (scanDesc [s.regs.rsi.toBitVec] ys n)) :
    Eventually (step e) P (state s a d (BitVec.ofNat 64 n - 1) y flags, base + 296) := by
  cases n with
  | zero => exact (mixed_zero e base hc s a d y flags P hp).2
  | succ n =>
    have hn0 : n = 0 := by omega
    subst n
    have hcpos : 0 < s.regs.rcx.toBitVec.toNat := by
      rw [hyc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ys.length < 2^64)]
      omega
    have hcarry : (-s.regs.rcx.toBitVec).unsigned ≠
        (0#64).unsigned - s.regs.rcx.toBitVec.unsigned := by
      simp only [BitVec.unsigned, BitVec.toNat_zero]
      omega
    have hload : Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 =
        some ((ys[0]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show 0 < ys.length by omega)] using hym ⟨0, by omega⟩
    have target226 := hc.targets ("natCompare_u226", 226) (by decide)
    have hp' : Exits e base s P (compare s.regs.rsi.toBitVec.toNat (ys[0]?.getD 0#64).toNat) := by
      simpa [scanDesc_one] using hp
    natcmp_step 86 using hc
    natcmp_step 87 using hc
    simp [StatusFlags.from_result, Effects.All]
    natcmp_step 88 using hc
    natcmp_step 89 using hc
    natcmp_step 90 using hc
    natcmp_step 91 using hc
    simp [StatusFlags.from_result, BitVec.unsigned]
    natcmp_step 92 using hc
    natcmp_step 93 using hc
    natcmp_step 94 using hc
    simp [StatusFlags.from_result, hcarry, Effects.All]
    natcmp_step 95 using hc
    natcmp_load hload
    natcmp_step 96 using hc
    natcmp_step 83 using hc
    natcmp_step 84 using hc
    natcmp_step 85 using hc
    by_cases he : s.regs.rsi.toBitVec = ys[0]?.getD 0#64
    · simp [StatusFlags.from_result, he, Effects.All]
      apply (mixed_zero e base hc s _ _ _ _ P _).2
      simpa [he] using hp'
    · simp [StatusFlags.from_result, he, target226, Effects.All]
      exact scan_unequal e base hc s _ _ _ _ _ P hp'

theorem small_small_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (n : Nat) (hn : n ≤ 1)
    (a d y : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (hp : Exits e base s P (scanDesc [s.regs.rsi.toBitVec] [s.regs.rcx.toBitVec] n)) :
    Eventually (step e) P (state s a d (BitVec.ofNat 64 n) y flags, base + 364) := by
  have zero (a d y : BitVec 64) (fl : StatusFlags) (hp : Exits e base s P .eq) :
      Eventually (step e) P (state s a d 0 y fl, base + 364) := by
    natcmp_step 103 using hc
    natcmp_step 104 using hc
    simp [StatusFlags.from_result]
    exact scan_zero e base hc s a d _ y _ P hp
  cases n with
  | zero => exact zero a d y flags hp
  | succ n =>
    have hn0 : n = 0 := by omega
    subst n
    have target336 := hc.targets ("natCompare_u336", 336) (by decide)
    have target226 := hc.targets ("natCompare_u226", 226) (by decide)
    have hp' : Exits e base s P (compare s.regs.rsi.toBitVec.toNat s.regs.rcx.toBitVec.toNat) := by
      simpa [scanDesc_one] using hp
    natcmp_step 103 using hc
    natcmp_step 104 using hc
    simp [StatusFlags.from_result, target336]
    natcmp_step 97 using hc
    natcmp_step 98 using hc
    natcmp_step 99 using hc
    natcmp_step 100 using hc
    natcmp_step 101 using hc
    natcmp_step 102 using hc
    by_cases he : s.regs.rsi.toBitVec = s.regs.rcx.toBitVec
    · simp [StatusFlags.from_result, he, Effects.All]
      apply zero
      simpa [he] using hp'
    · simp [StatusFlags.from_result, he, target226, Effects.All]
      exact scan_unequal e base hc s _ d _ _ _ P hp'

theorem scan_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (state s a d x y flags, if d = 0#64 then base + 278 else base + 136)) :
    Eventually (step e) P (state s a d x y flags, base + 127) := by
  have target := hc.targets ("natCompare_u278", 278) (by decide)
  natcmp_step 38 using hc
  constructor <;> natcmp_step 39 using hc
  all_goals
    by_cases hd : d = 0#64
    · simpa [StatusFlags.from_result, hd, target, state, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hd, state, Effects.All] using hp _

theorem large_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (state s a d (x-1) y flags,
        if s.regs.rdx.toBitVec = 0#64 then base + 263 else base + 172)) :
    Eventually (step e) P (state s a d x y flags, base + 136) := by
  have target := hc.targets ("natCompare_u172", 172) (by decide)
  natcmp_step 40 using hc
  natcmp_step 41 using hc
  constructor <;> natcmp_step 42 using hc
  all_goals
    by_cases hr : s.regs.rdx.toBitVec = 0#64
    · simp [StatusFlags.from_result, hr, Effects.All]
      natcmp_step 43 using hc
      simpa [hr, state] using hp _
    · simpa [StatusFlags.from_result, hr, target, state, Effects.All] using hp _

theorem small_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (state s a d (if s.regs.rdx.toBitVec = 0#64 then x else x-1) y flags,
        if s.regs.rdx.toBitVec = 0#64 then base + 364 else base + 296)) :
    Eventually (step e) P (state s a d x y flags, base + 278) := by
  have target := hc.targets ("natCompare_u364", 364) (by decide)
  natcmp_step 79 using hc
  constructor <;> natcmp_step 80 using hc
  all_goals
    by_cases hr : s.regs.rdx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hr, target, state, Effects.All] using hp _
    · simp [StatusFlags.from_result, hr, Effects.All]
      natcmp_step 81 using hc
      natcmp_step 82 using hc
      simpa [hr, state] using hp _

/-- All four representation combinations join the same descending-limb
specification, including zero significant length. -/
theorem equal_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (xs ys : List (BitVec 64))
    (hx : View s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec xs)
    (hy : View s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec ys)
    (n : Nat) (hxn : n ≤ xs.length) (hyn : n ≤ ys.length)
    (a y : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (hp : Exits e base s P (scanDesc xs ys n)) :
    Eventually (step e) P
      (state s a s.regs.rdi.toBitVec (BitVec.ofNat 64 n) y flags, base + 127) := by
  apply scan_dispatch e base hc
  intro fl
  rcases hx with ⟨hd, rfl⟩ | ⟨hd, hxc, hxb, hxm⟩
  · simp only [hd, ↓reduceIte]
    apply small_dispatch e base hc
    intro fl
    rcases hy with ⟨hr, rfl⟩ | ⟨hr, hyc, hyb, hym⟩
    · simp only [hr, ↓reduceIte]
      exact small_small_scan e base hc s n (by simpa using hxn) a 0 y fl P hp
    · simp only [hr, ↓reduceIte]
      exact small_large_scan e base hc s ys hyc hyb hym n (by simpa using hxn)
        hyn a 0 y fl P hp
  · simp only [hd, ↓reduceIte]
    apply large_dispatch e base hc
    intro fl
    rcases hy with ⟨hr, rfl⟩ | ⟨hr, hyc, hyb, hym⟩
    · simp only [hr, ↓reduceIte]
      exact large_small_scan e base hc s s.regs.rdi.toBitVec xs hxc hxb hxm n
        (by simpa using hyn) hxn a y fl P hp
    · simp only [hr, ↓reduceIte]
      exact large_scan e base hc s s.regs.rdi.toBitVec xs ys hxc hyc hxb hyb
        hxm hym P n hxn hyn a y fl hp

end SszX86.NatCompare
