import SszX86.NatDivisionCopyLoop

namespace SszX86.NatDivision.Copy
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Registers which remain unchanged throughout the copy, before the final NEG. -/
structure Stable (s t : MachineData) : Prop where
  rbx : get t .rbx = get s .rbx
  rbp : get t .rbp = get s .rbp
  r12 : get t .r12 = get s .r12
  r13 : get t .r13 = get s .r13
  rsp : get t .rsp = get s .rsp
  rsi : get t .rsi = get s .rsi
  rdx : get t .rdx = get s .rdx
  rdi : get t .rdi = get s .rdi
  vectors : t.zmms = s.zmms

/-- The reverse loop sees a fully initialized destination and remainder zero. -/
structure Ready (s t : MachineData) (destination : BitVec 64)
    (words : List (BitVec 64)) (count : Nat) : Prop where
  copied : t.dmem = memory s.dmem destination words count
  destination : get t .r14 = destination
  index : get t .rbp = -get s .rbp
  remainder : get t .r15 = 0
  divisor : get t .rbx = get s .rbx
  significant : get t .r13 = get s .r13
  arena : get t .r12 = get s .r12
  stack : get t .rsp = get s .rsp
  source : get t .rsi = get s .rsi
  length : get t .rdx = get s .rdx
  offset : get t .rdi = get s .rdi
  vectors : t.zmms = s.zmms

/-- The compiler's mask removes only the low count bit on its allocation domain. -/
theorem count_mask (count : Nat) (bound : count < 2^61) :
    2305843009213693950#64 &&& BitVec.ofNat 64 count =
      BitVec.ofNat 64 (count-count%2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show count < 2^64 by omega),
    Nat.mod_eq_of_lt (show count-count%2 < 2^64 by omega)]
  rw [show 2305843009213693950 % 2^64 = 2305843009213693950 by decide]
  have quotient : (2305843009213693950 &&& count) / 2 = count / 2 := by
    rw [Nat.and_div_two]
    change (2^60-1) &&& (count/2) = count/2
    rw [Nat.and_comm, Nat.and_two_pow_sub_one_of_lt_two_pow (by omega : count/2 < 2^60)]
  have remainder : (2305843009213693950 &&& count) % 2 = 0 := by
    have h := Nat.and_mod_two_pow (a := 2305843009213693950) (b := count) (n := 1)
    simpa using h
  omega

theorem odd_count (s : MachineData) (count : Nat) (rax : get s .rax = BitVec.ofNat 64 count) :
    odd s ↔ count%2 = 1 := by
  unfold odd
  rw [rax]
  have low : (((BitVec.ofNat 64 count).setWidth 8) &&& 1#8).toNat = count%2 := by
    simp [BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.and_one_is_mod, Nat.mod_mod_of_dvd]
  constructor
  · intro nonzero
    have ne : (((BitVec.ofNat 64 count).setWidth 8) &&& 1#8).toNat ≠ 0 := by
      intro eq
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      simpa using eq
    omega
  · intro one zero
    have eq := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat] at eq
    omega

/-- Complete tail from an already copied even prefix. -/
theorem finish_prefix_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (destination : BitVec 64) (words : List (BitVec 64)) (count : Nat)
    (bound : destination.toNat + 8*count ≤ 2^64) (lengthBound : words.length < 2^64)
    (stable : Stable s t)
    (countReg : get t .rax = BitVec.ofNat 64 count)
    (lengthReg : get s .rdx = BitVec.ofNat 64 words.length)
    (index : get t .r8 = BitVec.ofNat 64 (count-count%2))
    (pointer : get t .r14 = destination)
    (hprefix : t.dmem = memory s.dmem destination words (count-count%2))
    (loads : ∀ j, j < words.length →
      Mem.loadInt s.dmem (get s .rsi + BitVec.ofNat 64 (8*j)) 8 =
        some ((limb words j).toNat : Int))
    (hm : Large.Mapped s.dmem destination (8*count))
    (apart : Large.Disjoint (get s .rsi) destination (8*words.length) (8*count))
    (P : MachineState → Prop)
    (next : ∀ u, Ready s u destination words count → Eventually (step e) P (u, base + 768)) :
    Eventually (step e) P (t, base + 736) := by
  let q := count-count%2
  have qb : q < 2^64 := by dsimp [q]; omega
  have oddIff := odd_count t count countReg
  have address : get t .r14 + get t .r8 * 8#64 = destination + BitVec.ofNat 64 (8*q) := by
    rw [pointer, index]
    simp [q, BitVec.ofNat_mul, Nat.mul_comm]
  have source : get t .rsi + get t .r8 * 8#64 = get s .rsi + BitVec.ofNat 64 (8*q) := by
    rw [stable.rsi, index]
    simp [q, BitVec.ofNat_mul, Nat.mul_comm]
  have test : (get t .r8).toNat < (get t .rdx).toNat ↔ q < words.length := by
    rw [index, stable.rdx, lengthReg]
    simp [q, BitVec.toNat_ofNat, Nat.mod_eq_of_lt qb, Nat.mod_eq_of_lt lengthBound]
  apply tail_cps e base hc t (limb words q)
  · intro isOdd present
    rw [source, hprefix, memory_source s.dmem (get s .rsi) destination words count q
      (by dsimp [q]; omega) apart q (test.mp present)]
    exact loads q (test.mp present)
  · intro _ missing
    exact limb_missing words q (Nat.le_of_not_gt (fun h => missing (test.mpr h)))
  · intro isOdd
    have parity := oddIff.mp isOdd
    rw [address, hprefix]
    exact Large.mapped_load _ destination (8*count) (8*q) 8
      (memory_mapped s.dmem destination destination words q (8*count) hm)
      (by dsimp [q]; omega)
  · intro flags
    apply next
    by_cases isOdd : odd t
    · have parity := oddIff.mp isOdd
      have countEq : count = q+1 := by dsimp [q]; omega
      rw [ite_eq_left isOdd]
      refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stable.vectors⟩
      · change Mem.storeInt t.dmem (get t .r14 + get t .r8 * 8#64) 8 (limb words q).toInt =
          memory s.dmem destination words count
        rw [address]
        calc
          _ = memory s.dmem destination words (q+1) := by
            rw [memory_succ]
            exact congrArg (fun m => Mem.storeInt m (destination + BitVec.ofNat 64 (8*q))
              8 (limb words q).toInt) hprefix
          _ = memory s.dmem destination words count :=
            congrArg (memory s.dmem destination words) countEq.symm
      · simpa [finish, tailStore, get, Reg64s.get64] using pointer
      · simpa [finish, tailStore, get, Reg64s.get64] using congrArg Neg.neg stable.rbp
      · exact stable.rbx
      · exact stable.r13
      · exact stable.r12
      · exact stable.rsp
      · exact stable.rsi
      · exact stable.rdx
      · exact stable.rdi
    · have notOne : count%2 ≠ 1 := fun h => isOdd (oddIff.mpr h)
      have parity : count%2 = 0 := by omega
      simp only [isOdd, ↓reduceIte]
      refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stable.vectors⟩
      · simpa only [finish, parity, Nat.sub_zero] using hprefix
      · exact pointer
      · simpa [finish, get, Reg64s.get64] using congrArg Neg.neg stable.rbp
      · exact stable.rbx
      · exact stable.r13
      · exact stable.r12
      · exact stable.rsp
      · exact stable.rsi
      · exact stable.rdx
      · exact stable.rdi

/-- Actual PC627..768: count initialization, all unrolled pairs, possible odd
word, and reverse-loop setup. Source words are loaded physically and every
requested destination byte is written before the division continuation. -/
theorem copy_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (destination : BitVec 64) (words : List (BitVec 64)) (count : Nat)
    (positive : 0 < count) (countBound : count < 2^61)
    (bound : destination.toNat + 8*count ≤ 2^64) (lengthBound : words.length < 2^64)
    (countReg : get s .rax = BitVec.ofNat 64 count)
    (lengthReg : get s .rdx = BitVec.ofNat 64 words.length)
    (maskReg : get s .rcx = 2305843009213693950#64)
    (pointer : get s .r9 = destination)
    (arenaPointer : get s .r14 + get s .rdi = destination)
    (single : get s .rdx = get s .r8 + 1#64 ↔ count = 1)
    (loads : ∀ j, j < words.length →
      Mem.loadInt s.dmem (get s .rsi + BitVec.ofNat 64 (8*j)) 8 =
        some ((limb words j).toNat : Int))
    (hm : Large.Mapped s.dmem destination (8*count))
    (apart : Large.Disjoint (get s .rsi) destination (8*words.length) (8*count))
    (P : MachineState → Prop)
    (next : ∀ u, Ready s u destination words count → Eventually (step e) P (u, base + 768)) :
    Eventually (step e) P (s, base + 627) := by
  apply init_cps e base hc s P
  · intro one flags
    have countOne := single.mp one
    apply finish_prefix_cps e base hc s (initSingle s flags) destination words count
      bound lengthBound
    · constructor <;> rfl
    · exact countReg
    · exact lengthReg
    · simp [initSingle, get, Reg64s.get64, countOne]
    · simpa [initSingle, get, Reg64s.get64] using arenaPointer
    · simp [initSingle, countOne]
    · exact loads
    · exact hm
    · exact apart
    · exact next
  · intro notOne flags
    let q := count-count%2
    have notCountOne : count ≠ 1 := fun h => notOne (single.mpr h)
    have two : 2 ≤ q := by dsimp [q]; omega
    have qLe : q ≤ count := by dsimp [q]; omega
    have even : q%2 = 0 := by dsimp [q]; omega
    have loopCount : get (initPair s flags) .rcx = BitVec.ofNat 64 q := by
      change get s .rcx &&& get s .rax = _
      rw [maskReg, countReg]
      exact count_mask count countBound
    have loopPointer : get (initPair s flags) .r9 = destination + 8#64 := by
      change get s .r9 + 8#64 = _
      rw [pointer]
    have start : loopState (initPair s flags) destination words 0
        (get (initPair s flags) .r8) (get (initPair s flags) .r11) flags = initPair s flags := by
      simp [loopState, initPair, get, Reg64s.get64, memory]
    rw [← start]
    apply loop_cps e base hc (initPair s flags) destination words count q bound lengthBound
      qLe lengthReg loopCount loopPointer loads hm apart P
    · intro last endFlags
      apply exit_pair_cps e base hc
      intro tailFlags
      let t := exitPair (loopState (initPair s flags) destination words q
        (BitVec.ofNat 64 (q-2)) last endFlags) tailFlags
      apply finish_prefix_cps e base hc s t destination words count bound lengthBound
      · constructor <;> rfl
      · exact countReg
      · exact lengthReg
      · change BitVec.ofNat 64 (q-2) + 2#64 = BitVec.ofNat 64 q
        bv_omega
      · simpa [t, exitPair, loopState, initPair, get, Reg64s.get64] using arenaPointer
      · rfl
      · exact loads
      · exact hm
      · exact apart
      · exact next
    · omega
    · simpa using even

/-- The externally useful copied-word observation at reverse-division entry. -/
theorem Ready.load {s t : MachineData} {destination : BitVec 64}
    {words : List (BitVec 64)} {count : Nat} (ready : Ready s t destination words count)
    (bound : destination.toNat + 8*count ≤ 2^64) (i : Nat) (hi : i < count) :
    Mem.loadInt t.dmem (destination + BitVec.ofNat 64 (8*i)) 8 =
      some ((limb words i).toNat : Int) := by
  rw [ready.copied]
  exact memory_load s.dmem destination words count bound i hi

theorem Ready.frame {s t : MachineData} {destination : BitVec 64}
    {words : List (BitVec 64)} {count : Nat} (ready : Ready s t destination words count)
    (a : BitVec 64) (outside : ∀ i < 8*count, a ≠ destination + BitVec.ofNat 64 i) :
    t.dmem.get? a = s.dmem.get? a := by
  rw [ready.copied]
  exact memory_frame s.dmem destination a words count outside

end SszX86.NatDivision.Copy
