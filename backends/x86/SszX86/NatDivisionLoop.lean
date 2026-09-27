import SszX86.NatDivisionLoopMemory

namespace SszX86.NatDivision.Loop
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure Completed (s : MachineData) (words : List (BitVec 64)) (t : MachineData) : Prop where
  divisor : get t .rbx = get s .rbx
  count : get t .r13 = get s .r13
  destination : get t .r14 = get s .r14
  stack : get t .rsp = get s .rsp
  index : get t .rbp = -8#64
  remainder : (get t .r15).toNat =
    (SszNative.LimbDivision.loop (get s .rbx) words (get s .r15).toNat).2
  written : WordsAt t.dmem (get s .r14)
    (SszNative.LimbDivision.loop (get s .rbx) words (get s .r15).toNat).1
  frame : Frame s.dmem t.dmem (get s .r14) (get s .rsp) words.length
  vectors : t.zmms = s.zmms

private theorem reverse_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (rev : List (BitVec 64)) (s : MachineData)
    (hr : (get s .r15).toNat < (get s .rbx).toNat)
    (index : get s .rbp = BitVec.ofNat 64 (8*rev.length) - 8#64)
    (bound : (get s .r14).toNat + 8*rev.length ≤ 2^64)
    (loaded : WordsAt s.dmem (get s .r14) rev.reverse)
    (slot : ∃ old, Mem.loadInt s.dmem (get s .rsp - 8#64) 8 = some old)
    (apart : ∀ i < 8*rev.length, ∀ j < 8,
      get s .r14 + BitVec.ofNat 64 i ≠ get s .rsp - 8#64 + BitVec.ofNat 64 j)
    (P : MachineState → Prop)
    (next : ∀ t, Completed s rev.reverse t → Eventually (step e) P (t, base + 477)) :
    Eventually (step e) P (s, if rev = [] then base + 477 else base + 768) := by
  induction rev generalizing s with
  | nil =>
    apply next s
    constructor
    · rfl
    · rfl
    · rfl
    · rfl
    · simpa using index
    · rfl
    · intro i hi; simp [SszNative.LimbDivision.loop] at hi
    · intro a _ _; rfl
    · rfl
  | cons limb rev ih =>
    let d := get s .rbx
    let r := SszNative.LimbDivision.step d (get s .r15).toNat limb
    have hd : d ≠ 0 := by intro h; simp [d, h] at hr
    have remBound : r.2 < d.toNat := SszNative.LimbDivision.step_remainder_lt _ _ _ hd
    have remCast : (BitVec.ofNat 64 r.2).toNat = r.2 := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans remBound d.isLt)]
    have idx : get s .rbp = BitVec.ofNat 64 (8*rev.length) := by
      rw [index]
      simp only [List.length_cons]
      have eq : 8*(rev.length+1) = 8*rev.length+8 := by omega
      rw [eq, BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have wordLoad : Mem.loadInt s.dmem (get s .r14 + get s .rbp) 8 =
        some (limb.toNat : Int) := by
      rw [idx]
      simpa [List.reverse_cons] using loaded rev.length (by simp)
    have wordSlot : ∀ i < 8, ∀ j < 8,
        get s .r14 + get s .rbp + BitVec.ofNat 64 i ≠
          get s .rsp - 8#64 + BitVec.ofNat 64 j := by
      intro i hi j hj
      rw [idx, memmove_addr_add]
      exact apart _ (by simp only [List.length_cons]; omega) j hj
    simp only [List.cons_ne_nil, reduceIte]
    apply iteration_cps e base hc hdiv s limb hr wordLoad slot wordSlot P
    intro t ht
    have tRem : (get t .r15).toNat = r.2 := by
      rw [ht.remainder]
      exact remCast
    have tLoaded : WordsAt t.dmem (get t .r14) rev.reverse := by
      intro i hi
      rw [ht.destination, ht.memory, idx]
      rw [BoolCodec.load_store_disjoint _ _ _ 8 8 _
        (word_apart (get s .r14) (rev.length+1) i rev.length
          (by simpa using bound) (by simpa using Nat.lt_succ_of_lt hi) (by omega)
          (by simpa using Nat.ne_of_lt hi))]
      rw [BoolCodec.load_store_disjoint _ _ _ 8 8 _ (by
        intro a ha b hb
        rw [memmove_addr_add]
        exact apart _ (by simp only [List.length_cons] at *; simp only [List.length_reverse] at hi; omega) b hb)]
      simpa [List.reverse_cons, List.getElem_append_left hi] using
        loaded i (by simp only [List.length_reverse, List.length_cons] at *; omega)
    have tSlot : Mem.loadInt t.dmem (get t .rsp - 8#64) 8 =
        some ((base + 789).toBitVec.toNat : Int) := by
      rw [ht.stack, ht.memory]
      rw [BoolCodec.load_store_disjoint _ _ _ 8 8 _ (by
        intro a ha b hb equal
        exact wordSlot b hb a ha equal.symm)]
      exact load_word_store _ _ _
    have tIndex : get t .rbp = BitVec.ofNat 64 (8*rev.length) - 8#64 := by
      rw [ht.index, idx]
    have tBound : (get t .r14).toNat + 8*rev.length ≤ 2^64 := by
      rw [ht.destination]
      simp only [List.length_cons] at bound
      omega
    have tApart : ∀ i < 8*rev.length, ∀ j < 8,
        get t .r14 + BitVec.ofNat 64 i ≠ get t .rsp - 8#64 + BitVec.ofNat 64 j := by
      rw [ht.destination, ht.stack]
      intro i hi j hj
      exact apart i (by simp only [List.length_cons]; omega) j hj
    have branch : (get s .rbp = 0) ↔ rev = [] := by
      rw [idx, ← List.length_eq_zero_iff]
      have small : 8*rev.length < 2^64 := by simp only [List.length_cons] at bound; omega
      constructor
      · intro equal
        have eq := congrArg BitVec.toNat equal
        change (8*rev.length) % 2^64 = 0 at eq
        rw [Nat.mod_eq_of_lt small] at eq
        omega
      · intro equal; simp [equal]
    simp only [branch]
    apply ih t (by rw [ht.divisor, tRem]; exact remBound)
      tIndex tBound tLoaded ⟨_, tSlot⟩ tApart
    intro u hu
    have recurrence : SszNative.LimbDivision.loop (get s .rbx) (limb :: rev).reverse
        (get s .r15).toNat =
        ((SszNative.LimbDivision.loop (get t .rbx) rev.reverse (get t .r15).toNat).1 ++ [r.1],
          (SszNative.LimbDivision.loop (get t .rbx) rev.reverse (get t .r15).toNat).2) := by
      simp [List.reverse_cons, SszNative.LimbDivision.loop_append,
        SszNative.LimbDivision.loop, ht.divisor, tRem, r, d]
    apply next u
    constructor
    · exact hu.divisor.trans ht.divisor
    · exact hu.count.trans ht.count
    · exact hu.destination.trans ht.destination
    · exact hu.stack.trans ht.stack
    · exact hu.index
    · rw [recurrence]; exact hu.remainder
    · rw [recurrence]
      intro i hi
      by_cases lower : i < rev.length
      · have lowLen := SszNative.LimbDivision.loop_length (get t .rbx) rev.reverse (get t .r15).toNat
        have low : i < (SszNative.LimbDivision.loop (get t .rbx) rev.reverse (get t .r15).toNat).1.length := by
          simpa [lowLen] using lower
        simpa [ht.destination, List.getElem_append_left low] using hu.written i low
      · have eq : i = rev.length := by
          simp only [List.length_append, List.length_singleton,
            SszNative.LimbDivision.loop_length, List.length_reverse] at hi
          omega
        subst i
        have kept : Mem.loadInt u.dmem (get s .r14 + BitVec.ofNat 64 (8*rev.length)) 8 =
            Mem.loadInt t.dmem (get s .r14 + BitVec.ofNat 64 (8*rev.length)) 8 := by
          apply frame_load t.dmem u.dmem (get t .r14) (get t .rsp) _ rev.length 8
            (by simpa using hu.frame)
          · intro a ha b hb
            rw [ht.destination, memmove_addr_add]
            intro equal
            have inj := memmove_addr_injective (get s .r14) (8*(rev.length+1))
              (8*rev.length+a) b (by simpa using bound) (by omega) (by omega) equal
            omega
          · simpa [ht.stack, idx] using wordSlot
        rw [kept, ht.memory, idx, load_word_store]
        simp [SszNative.LimbDivision.loop_length, r, d]
    · have first := iteration_frame s t (base + 789).toBitVec limb ht (get s .r14) rev.length rfl idx
      have second : Frame t.dmem u.dmem (get s .r14) (get s .rsp) rev.length := by
        simpa [ht.destination, ht.stack] using hu.frame
      simpa using frame_trans s.dmem t.dmem u.dmem (get s .r14) (get s .rsp)
        rev.length (rev.length+1) (by omega) first second
    · exact hu.vectors.trans ht.vectors

/-- Complete arbitrary-count reverse division through the actual linked runtime
helper. The only size condition is the physical destination range. -/
theorem loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (words : List (BitVec 64)) (positive : 0 < words.length)
    (hr : (get s .r15).toNat < (get s .rbx).toNat)
    (index : get s .rbp = BitVec.ofNat 64 (8*(words.length-1)))
    (bound : (get s .r14).toNat + 8*words.length ≤ 2^64)
    (loaded : WordsAt s.dmem (get s .r14) words)
    (slot : ∃ old, Mem.loadInt s.dmem (get s .rsp - 8#64) 8 = some old)
    (apart : ∀ i < 8*words.length, ∀ j < 8,
      get s .r14 + BitVec.ofNat 64 i ≠ get s .rsp - 8#64 + BitVec.ofNat 64 j)
    (P : MachineState → Prop)
    (next : ∀ t, Completed s words t → Eventually (step e) P (t, base + 477)) :
    Eventually (step e) P (s, base + 768) := by
  have indexed : get s .rbp = BitVec.ofNat 64 (8*words.reverse.length) - 8#64 := by
    rw [index, List.length_reverse]
    have eq : 8*words.length = 8*(words.length-1)+8 := by omega
    rw [eq, BitVec.ofNat_add]
    exact (BitVec.add_sub_cancel _ _).symm
  have nonempty : words.reverse ≠ [] := by
    intro h
    have lengthZero : words.length = 0 := by
      simpa only [List.length_reverse, List.length_nil] using congrArg List.length h
    omega
  simpa only [List.reverse_reverse, nonempty, reduceIte] using
    reverse_cps e base hc hdiv words.reverse s hr indexed (by simpa using bound)
      (by simpa using loaded) slot (by simpa using apart) P (by simpa using next)

end SszX86.NatDivision.Loop
