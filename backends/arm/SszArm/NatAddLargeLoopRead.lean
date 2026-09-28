import SszArm.NatAddLargeLoopSelect

namespace SszArm.NatAdd.LargeLoop

open NatCompare (Source Words saved)
open Delimited (Span Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def pureOps : List Op :=
  [.p1604, .p1608, .p1612, .p1616, .p1620, .p1624,
   .p1660, .p1664, .p1668, .p1672, .p1676, .p1680, .p1684, .p1688,
   .p1692, .p1696, .p1796, .p1860, .p1864]

theorem pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (writes : List Span) (hs : ∀ op ∈ ops, op ∈ pureOps) :
    LoopFrame writes s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact LoopFrame.refl writes s
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    have hf : LoopFrame writes s (op.effect base s) := by
      cases op <;> simp_all only [pureOps, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · intro a ha
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop)))

theorem load_frame (s : ArmState) (base word : BitVec 64) (kind : LoadKind)
    (writes : List Span) (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes)
    (hk : kind ∈ [.loopLeft, .loopRight, .loopRightSmall]) :
    LoopFrame writes s (loadResult s base kind word) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [loadResult, saved, state_simp_rules]
  · simp [loadResult, saved, state_simp_rules]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    cases kind <;> simp_all [loadResult, LoadKind.dst, saved, state_simp_rules]
  · intro reg; simp [loadResult, saved, state_simp_rules]
  · intro a outside
    have separate := outside _ slot
    simpa [loadResult, saved, LoadKind.tmp, state_simp_rules] using
      BoolCodec.write_mem_bytes_frame s (r (.GPR 31#5) s - 16#64) 8
        (r (.GPR kind.tmp) s) a (by bv_omega) (by bv_omega)

def leftState (s : ArmState) (base : BitVec 64) (left : List (BitVec 64))
    (index : Nat) : ArmState :=
  if index < left.length then
    loadResult (block base [.p1692, .p1696] s) base .loopLeft (left[index]?.getD 0)
  else block base [.p1692, .p1696, .p1796] s

def leftGate (left : List (BitVec 64)) (index : Nat) : GateKind :=
  if index < left.length then .loaded else .zero

theorem left_run (s : ArmState) (base pointer : BitVec 64)
    (left : List (BitVec 64)) (index : Nat) (writes : List Span)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1692#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : (r (.GPR 2#5) s).toNat = left.length)
    (h15 : (r (.GPR 15#5) s).toNat = index)
    (hs : Source s pointer left) (hm : Words s pointer left)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes) :
    let t := leftState s base left index
    run (if index < left.length then 10 else 3) s = t ∧
    LoopFrame writes s t ∧
    read_pc t = base + BitVec.ofNat 64 (leftGate left index).start ∧
    r (.GPR 16#5) t = left[index]?.getD 0 ∧
    (∀ reg : BitVec 5, reg ≠ 16#5 → r (.GPR reg) t = r (.GPR reg) s) := by
  have hpc : r .PC s = base + 1692#64 := hp
  have flag := Udivti3.cmp_carry (r (.GPR 15#5) s) (r (.GPR 2#5) s)
  by_cases within : index < left.length
  · let u := block base [.p1692, .p1696] s
    have uf : LoopFrame writes s u := pure_frame base [.p1692, .p1696] s writes (by decide)
    have noCarry : (AddWithCarry (r (.GPR 15#5) s) (~~~r (.GPR 2#5) s) 1#1).2.c ≠ 1#1 := by
      intro carry
      have less := flag.mp carry
      rw [h2, h15] at less
      omega
    have follows : Follows base [.p1692, .p1696] s := by
      simp [Follows, Op.row, Op.effect, Udivti3.compare,
        Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]
    have urun : run 2 s = u := block_run base _ s hc he ha follows
    have up : read_pc u = base + 1700#64 := by
      simp [u, block, Op.effect, Udivti3.compare,
        Udivti3.next, state_simp_rules, noCarry]
    have us : Source u pointer left := uf.source _ _ hs
    have um : Words u pointer left := by
      intro i
      simpa [u, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules] using hm i
    have u1 : r (.GPR 1#5) u = pointer := (uf.registers _ (by decide)).trans h1
    have u15 : r (.GPR 15#5) u = BitVec.ofNat 64 index := by
      have original : r (.GPR 15#5) s = BitVec.ofNat 64 index := by
        rw [← h15]
        simp
      simpa [u, block, Op.effect, Udivti3.compare,
        Udivti3.next, state_simp_rules] using original
    have load : read_mem_bytes 8
        (r (.GPR LoadKind.loopLeft.ptr) u + (r (.GPR LoadKind.loopLeft.index) u <<< 3))
        (saved u LoadKind.loopLeft.tmp) = left[index]?.getD 0 := by
      simp only [LoadKind.ptr, LoadKind.index, u1, u15]
      exact NatCompare.limb_load u pointer left index _ within us um
    have vrun := NatAdd.load_run u base _ .loopLeft (uf.code hc)
      (uf.error.trans he) (uf.aligned ha) up us.1 load
    have vf := load_frame u base (left[index]?.getD 0) .loopLeft writes us.1
      (by simpa only [uf.sp] using slot) (by decide)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [leftState, within, ↓reduceIte]
      rw [show 10 = 2 + 8 by decide, run_plus, urun]
      exact vrun
    · simpa only [leftState, within, ↓reduceIte] using uf.trans vf
    · simp [leftState, leftGate, within, loadResult, LoadKind.start, GateKind.start,
        state_simp_rules]
    · simp [leftState, within, loadResult, LoadKind.dst, state_simp_rules]
    · intro reg hr
      simp [leftState, within, loadResult, LoadKind.dst, saved,
        block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules, hr]
  · have zero : left[index]?.getD 0 = 0 := by
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have carry : (AddWithCarry (r (.GPR 15#5) s) (~~~r (.GPR 2#5) s) 1#1).2.c = 1#1 := by
      apply flag.mpr
      rw [h2, h15]
      omega
    have follows : Follows base [.p1692, .p1696, .p1796] s := by
      simp [Follows, Op.row, Op.effect, Udivti3.compare,
        Udivti3.next, state_simp_rules, hpc, carry, BitVec.add_assoc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [leftState, within, ↓reduceIte, List.length_cons, List.length_nil,
        Nat.reduceAdd] using
        block_run base [.p1692, .p1696, .p1796] s hc he ha follows
    · simpa only [leftState, within, ↓reduceIte] using
        pure_frame base [.p1692, .p1696, .p1796] s writes (by decide)
    · simp [leftState, leftGate, within, GateKind.start, block, Op.effect,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules, carry, BitVec.add_assoc]
    · rw [zero]
      simp [leftState, within, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro reg hr
      simp [leftState, within, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, hr]

end SszArm.NatAdd.LargeLoop
