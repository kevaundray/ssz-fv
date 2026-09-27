import SszArm.NatDivisionMemory
import SszArm.NatCompareMemory

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Only the lowering spill and quotient payload are writable in this phase. -/
def loopWrites (sp pointer : BitVec 64) (count : Nat) : List Span :=
  [(sp.toNat - 16, 16), (pointer.toNat, 8 * count)]

/-- The physical requirements for an in-place reverse pass. -/
structure LoopSpace (sp pointer : BitVec 64) (count : Nat) : Prop where
  stack : 16 ≤ sp.toNat
  physical : pointer.toNat + 8 * count ≤ 2^64
  apart : pointer.toNat + 8 * count ≤ sp.toNat - 16 ∨ sp.toNat ≤ pointer.toNat

/-- Every position is observed, including zero high quotient words. -/
def LoopWords (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64)) : Prop :=
  ∀ i (hi : i < words.length),
    read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * i)) s = words[i]

structure LoopFrame (writes : List Span) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, 9 ≤ reg.toNat → reg ≠ 21#5 → reg ≠ 23#5 →
    reg ≠ 30#5 → r (.GPR reg) t = r (.GPR reg) s
  sfp : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : MemoryFrame writes s t

theorem LoopFrame.refl (writes : List Span) (s : ArmState) : LoopFrame writes s s :=
  ⟨rfl, rfl, fun _ _ _ _ _ => rfl, fun _ => rfl, MemoryFrame.refl _ _⟩

theorem LoopFrame.trans {writes : List Span} {s t u : ArmState}
    (h : LoopFrame writes s t) (k : LoopFrame writes t u) : LoopFrame writes s u :=
  ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg lo h21 h23 h30 => (k.registers reg lo h21 h23 h30).trans
      (h.registers reg lo h21 h23 h30),
    fun reg => (k.sfp reg).trans (h.sfp reg), h.memory.trans k.memory⟩

theorem LoopFrame.sp {writes : List Span} {s t : ArmState} (h : LoopFrame writes s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide) (by decide) (by decide) (by decide)

theorem LoopFrame.aligned {writes : List Span} {s t : ArmState}
    (h : LoopFrame writes s t) (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

def loopSpill (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s

def loopAddress (s : ArmState) : BitVec 64 := r (.GPR 24#5) s + r (.GPR 23#5) s

theorem loopSpill_read (s : ArmState) (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (loopSpill s) = r (.GPR 9#5) s := by
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)

theorem loopSpill_frame (s : ArmState) (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s (loopSpill s) := by
  intro a outside
  have ha := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ a (by bv_omega) (by bv_omega)

theorem LoopSpace.address {sp pointer : BitVec 64} {count i : Nat}
    (space : LoopSpace sp pointer count) (hi : i < count) :
    (pointer + BitVec.ofNat 64 (8 * i)).toNat = pointer.toNat + 8 * i := by
  have hp := pointer.isLt
  have bound := space.physical
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem LoopSpace.prefix {sp pointer : BitVec 64} {count n : Nat}
    (space : LoopSpace sp pointer count) (hn : n ≤ count) : LoopSpace sp pointer n :=
  ⟨space.stack, by have := space.physical; omega,
    by have := space.apart; omega⟩

theorem loopSpill_word (s : ArmState) (count i : Nat)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) :
    read_mem_bytes 8 (r (.GPR 24#5) s + BitVec.ofNat 64 (8 * i)) (loopSpill s) =
      read_mem_bytes 8 (r (.GPR 24#5) s + BitVec.ofNat 64 (8 * i)) s := by
  apply (loopSpill_frame s space.stack).read
  · rw [space.address hi]; have := space.physical; omega
  · rw [space.address hi]
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    have := space.apart
    have := space.stack
    simp only [Prod.fst, Prod.snd]
    omega

theorem LoopWords.append (s : ArmState) (pointer : BitVec 64)
    (low high : List (BitVec 64)) :
    LoopWords s pointer (low ++ high) ↔
      LoopWords s pointer low ∧
      ∀ i (hi : i < high.length),
        read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * (low.length + i))) s = high[i] := by
  constructor
  · intro h
    constructor
    · intro i hi
      have observed := h i (by simp; omega)
      change read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * i)) s =
        (low ++ high)[i]'(by simp only [List.length_append]; omega) at observed
      rw [List.getElem_append_left hi] at observed
      exact observed
    · intro i hi
      have observed := h (low.length + i) (by simp; omega)
      change read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * (low.length + i))) s =
        (low ++ high)[low.length + i]'(by simp only [List.length_append]; omega) at observed
      rw [List.getElem_append_right (by omega)] at observed
      simpa only [Nat.add_sub_cancel_left] using observed
  · rintro ⟨lo, high⟩ i hi
    by_cases h : i < low.length
    · simpa only [List.getElem_append_left h] using lo i h
    · rw [List.getElem_append_right (by omega)]
      have hh := high (i - low.length) (by simp only [List.length_append] at hi; omega)
      simpa only [Nat.add_sub_of_le (by omega : low.length ≤ i)] using hh

end SszArm.NatDivision
