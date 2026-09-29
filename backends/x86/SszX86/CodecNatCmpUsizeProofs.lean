import SszX86.CodecNatCmpUsizePrepare

namespace SszX86.CodecNatCmpUsize
open SszNative.Limbs SszNative.NatABI

private theorem borrowed_words_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (a c : BitVec 64) (flags : StatusFlags)
    (count : s.regs.rsi.toBitVec = BitVec.ofNat 64 words.length)
    (bound : words.length + 1 < 2^64) (positive : 0 < words.length)
    (loads : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (state s (words[0]?.getD 0) (words[1]?.getD 0) (words[0]?.getD 0) flags,
        base + 81)) :
    Eventually (step e) P (state s a c s.regs.rsi.toBitVec flags, base + 55) := by
  have countNat : s.regs.rsi.toNat = words.length := by
    have h := congrArg BitVec.toNat count
    simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show words.length < 2^64 by omega)] using h
  apply borrowed_cps e base hc s a c (words[0]?.getD 0) (words[1]?.getD 0) flags
  · simpa [List.getElem?_eq_getElem positive] using loads ⟨0, positive⟩
  · intro two
    have two' : 1 < words.length := by omega
    simpa [List.getElem?_eq_getElem two'] using loads ⟨1, two'⟩
  · intro fl
    by_cases short : s.regs.rsi.toNat < 2
    · have absent : words[1]?.getD 0#64 = 0 := by
        rw [List.getElem?_eq_none (by omega)]
        rfl
      simpa [short, absent] using next fl
    · simpa [short] using next fl

def Exits (e : Executable) (base : Int64) (s : MachineData)
    (P : MachineState → Prop) (ord : Ordering) : Prop :=
  ∀ a c v flags, a.setWidth 8 = orderingByte ord →
    Eventually (step e) P (state s a c v flags, base + 45) ∧
    Eventually (step e) P (state s a c v flags, base + 101)

/-- Every Small and raw Large operand is admitted, including empty and padded
Large values. Read-only aliases are unrestricted. -/
theorem words_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (view : NatCompare.View s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec words)
    (P : MachineState → Prop)
    (next : Exits e base s P (compare (SszNative.Limbs.value words) s.regs.rdx.toNat)) :
    Eventually (step e) P (s, base) := by
  rcases view with ⟨pointer, rfl⟩ | ⟨pointer, count, bound, loads⟩
  · apply entry_cps e base hc s P
    · intro _ flags
      apply encode_cps e base hc s _ 0 _ flags P
      intro a c fl result
      apply (next a c s.regs.rsi.toBitVec fl _).2
      simpa [SszNative.Limbs.value] using result
    · intro nonzero
      exact False.elim (nonzero pointer)
  · have lengthNat : s.regs.rsi.toNat = words.length := by
      have h := congrArg BitVec.toNat count
      simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show words.length < 2^64 by omega)] using h
    have sigBound : sigWords words < 2^64 := by
      have h := sigWords_le_length words
      omega
    have lowFinish (fits : sigWords words ≤ 2) (a c : BitVec 64) (flags : StatusFlags)
        (positive : 0 < words.length) :
        Eventually (step e) P (state s a c s.regs.rsi.toBitVec flags, base + 55) := by
      apply borrowed_words_cps e base hc s words a c flags count bound positive loads P
      intro fl
      apply encode_cps e base hc s _ _ _ fl P
      intro a' c' fl' result
      apply (next a' c' (words[0]?.getD 0) fl' _).2
      simpa only [width_two_value words fits] using result
    apply entry_cps e base hc s P
    · intro zero
      exact False.elim (pointer zero)
    · intro _ flags
      have plus : s.regs.rsi.toBitVec + 1 = BitVec.ofNat 64 (words.length+1) := by
        rw [count]
        bv_omega
      rw [plus]
      apply scan_cps e base hc s words bound loads P words.length (Nat.le_refl _) _ flags
      · intro zero c fl
        apply zero_cps e base hc s 1 c fl P
        · intro empty fl'
          have nil : words = [] := by
            apply List.length_eq_zero_iff.mp
            have hz := congrArg BitVec.toNat empty
            change s.regs.rsi.toNat = 0 at hz
            omega
          apply encode_cps e base hc s 1 0 0 fl' P
          intro a' c' fl'' result
          apply (next a' c' 0 fl'' _).2
          simpa [nil, SszNative.Limbs.value] using result
        · intro nonempty fl'
          apply lowFinish (by change significantCount words words.length ≤ 2; omega) 1 c fl'
          by_contra hn
          have len : words.length = 0 := by omega
          apply nonempty
          rw [count, len]
          rfl
      · intro positive fl
        apply count_cps e base hc s _ _ fl P
        · intro fits fl'
          have fits' : sigWords words ≤ 2 := by
            simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound] using
              (show (BitVec.ofNat 64 (sigWords words)).toNat ≤ 2 by omega)
          apply lowFinish fits' _ _ fl'
          have h := sigWords_le_length words
          change 0 < sigWords words at positive
          omega
        · intro many fl'
          have many' : 2 < sigWords words := by
            simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound] using many
          have huge : 2^(64*2) ≤ SszNative.Limbs.value words := by
            by_contra hn
            have fits := (SszNative.NatOperand.wordCount_le_iff_value_lt
              (.large s.regs.rdi.toBitVec words) 2).2 (by
                change SszNative.Limbs.value words < 2^(64*2)
                omega)
            change sigWords words ≤ 2 at fits
            omega
          have greater : s.regs.rdx.toNat < SszNative.Limbs.value words := by
            have h := s.regs.rdx.toBitVec.isLt
            change s.regs.rdx.toNat < 2^64 at h
            simp only [Nat.reduceMul, Nat.reducePow] at huge
            omega
          apply (next _ _ _ fl' _).1
          simp [Nat.compare_eq_ite_lt, show ¬SszNative.Limbs.value words < s.regs.rdx.toNat by omega,
            greater, orderingByte, BitVec.replaceLow, BitVec.drop,
            BitVec.setWidth_append_eq_right]

def Returned (s : MachineData) (ra : BitVec 64) (ord : Ordering) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  t.1.regs.rax.toBitVec.setWidth 8 = orderingByte ord ∧
  t.1.dmem = s.dmem ∧ t.1.zmms = s.zmms ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r

/-- Full entry-to-return refinement with the exact original memory and complete
SysV callee-saved register set preserved. There is no allocator or stack write. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (lhs : Nat) (ra : BitVec 64)
    (operand : SszNative.NatMemory.Pair (UintCodec.widthLoad s.dmem)
      s.regs.rdi.toBitVec s.regs.rsi.toBitVec lhs)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step e) (Returned s ra (compare lhs s.regs.rdx.toNat)) (s, base) := by
  obtain ⟨words, view, value⟩ := NatCompare.pair_view s.dmem _ _ lhs operand
  apply words_runs e base hc s words view
  rw [value]
  intro a c v flags result
  apply ret_cps e base hc (state s a c v flags) ra _ ret
  refine ⟨rfl, result, rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4
  cases r <;> simp_all [state, Reg64s.get64]

end SszX86.CodecNatCmpUsize
