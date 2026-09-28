import SszArm.NatAddSmallLoopFrame

namespace SszArm.NatAdd.SmallLoop

open UintCodec SszNative
open NatCompare (Source Words saved)
open Delimited (Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem read_register (s : ArmState) (base : BitVec 64) (right : List (BitVec 64))
    (index : Nat) (reg : BitVec 5) (hr : reg ≠ 15#5) :
    r (.GPR reg) (readState s base right index) = r (.GPR reg) s := by
  by_cases present : index < right.length <;>
    simp [readState, present, loadResult, LoadKind.dst, LoadKind.tmp,
      block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      saved, state_simp_rules, hr]

theorem tail_memory (s : ArmState) (base : BitVec 64) :
    (tailState s base).mem = s.mem := by
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp [tailState, tailOps, carry, block, Op.effect, put, next, state_simp_rules]

def addState (s : ArmState) (base : BitVec 64)
    (right : List (BitVec 64)) (index : Nat) : ArmState :=
  block base [.p1912, .p1916] (readState s base right index)

def roundState (s : ArmState) (base : BitVec 64)
    (right : List (BitVec 64)) (index : Nat) : ArmState :=
  tailState (storeResult (addState s base right index) base .small) base

def roundFuel (s : ArmState) (base : BitVec 64)
    (right : List (BitVec 64)) (index : Nat) : Nat :=
  readFuel right index + 2 + 8 +
    (tailOps (decide (r (.FLAG .C)
      (storeResult (addState s base right index) base .small) = 1#1))).length

/-- One complete round is the real bounds-check/load, ADDS, indexed store with
X10 spill/restore, carry materialization, SUBS and back edge. -/
theorem round_run (s : ArmState) (base pointer sp output : BitVec 64)
    (right : List (BitVec 64)) (allocated index remaining carry : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1980#64)
    (h3 : r (.GPR 3#5) s = pointer)
    (h4 : r (.GPR 4#5) s = BitVec.ofNat 64 right.length)
    (h9 : r (.GPR 9#5) s = output)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 carry)
    (h13 : r (.GPR 13#5) s = BitVec.ofNat 64 (remaining + 1))
    (h14 : r (.GPR 14#5) s = BitVec.ofNat 64 index)
    (hsp : r (.GPR 31#5) s = sp)
    (layout : Layout sp output allocated) (fit : index + (remaining + 1) ≤ allocated)
    (carryBound : carry ≤ 1) (source : Source s pointer right) (words : Words s pointer right) :
    let next := LimbAdd.step 0#64 (right[index]?.getD 0#64) carry
    let t := roundState s base right index
    run (roundFuel s base right index) s = t ∧
      LoopFrame (writes sp output index (remaining + 1)) s t ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 next.2 ∧
      r (.GPR 13#5) t = BitVec.ofNat 64 remaining ∧
      r (.GPR 14#5) t = BitVec.ofNat 64 (index + 1) ∧
      read_pc t = base + (if remaining = 0 then 2044#64 else 1980#64) ∧
      read_mem_bytes 8 (address output index) t = next.1 := by
  have hi : index < allocated := by omega
  have hi64 : index < 2^64 := by have := layout.physical; omega
  have hr64 : remaining + 1 < 2^64 := by have := layout.physical; omega
  have addressNat := address_nat layout hi
  have physical : (address output index).toNat + 8 ≤ 2^64 := by
    rw [addressNat]
    have := layout.physical
    omega
  let regions := writes sp output index (remaining + 1)
  let v := readState s base right index
  obtain ⟨runRead, vp, v15⟩ := right_read s base pointer right index hc he ha hp
    h3 h4 h14 hi64 source words
  have vf : LoopFrame regions s v := read_frame s base sp output right index _ hsp layout.stack
  have v9 : r (.GPR 9#5) v = output := (read_register s base right index _ (by decide)).trans h9
  have v12 : r (.GPR 12#5) v = BitVec.ofNat 64 carry :=
    (read_register s base right index _ (by decide)).trans h12
  have v13 : r (.GPR 13#5) v = BitVec.ofNat 64 (remaining + 1) :=
    (read_register s base right index _ (by decide)).trans h13
  have v14 : r (.GPR 14#5) v = BitVec.ofNat 64 index :=
    (read_register s base right index _ (by decide)).trans h14
  change read_pc v = base + 1912#64 at vp
  change r (.GPR 15#5) v = right[index]?.getD 0#64 at v15
  have vpc : r .PC v = base + 1912#64 := vp
  let u := block base [.p1912, .p1916] v
  have runAdd : run 2 v = u := block_run base [.p1912, .p1916] v (vf.code hc) (vf.error.trans he)
    (vf.aligned ha) (by
      simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, vpc, BitVec.add_assoc])
  have uf : LoopFrame regions v u := readonly_frame base _ v regions (by decide)
  have up : read_pc u = base + 1920#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, vpc, BitVec.add_assoc]
  have u9 : r (.GPR 9#5) u = output := (uf.registers _ (by decide)).trans v9
  have u14 : r (.GPR 14#5) u = BitVec.ofNat 64 index := by
    simp [u, block, Op.effect, put, next, state_simp_rules, v14]
  have u13 : r (.GPR 13#5) u = BitVec.ofNat 64 (remaining + 1) := by
    simp [u, block, Op.effect, put, next, state_simp_rules, v13]
  have usp : r (.GPR 31#5) u = sp := uf.sp.trans (vf.sp.trans hsp)
  have ua : storeAddress u .small = address output index := by
    simp [storeAddress, StoreKind.index, u9, u14, address_shift]
  have u15 : r (.GPR 15#5) u = (LimbAdd.step 0#64 (right[index]?.getD 0#64) carry).1 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, v12, v15,
      add_low _ _ carryBound]
  have u16 : r (.GPR 16#5) u = BitVec.ofNat 64 (index + 1) := by
    simp [u, block, Op.effect, put, next, state_simp_rules, v14, BitVec.ofNat_add]
  have uCarry : r (.FLAG .C) u =
      (AddWithCarry (BitVec.ofNat 64 carry) (right[index]?.getD 0#64) 0#1).2.c := by
    simp [u, block, Op.effect, put, next, state_simp_rules, v12, v15]
  have restore := store_restore u .small (by simpa [usp] using layout.stack)
    (by simpa [ua] using physical) (by
      right
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst span
      rw [ua, addressNat, usp]
      have := layout.stack
      have := layout.separate
      bv_omega)
  let w := storeResult u base .small
  have runStore : run 8 u = w := store_run u base .small ((vf.trans uf).code hc)
    ((vf.trans uf).error.trans he) ((vf.trans uf).aligned ha) up restore
  have wf : LoopFrame regions u w := store_frame u base .small regions
    (by simpa [usp] using layout.stack) (by simpa [ua] using physical)
    (by simp [regions, writes, usp]) (by
      intro a low high
      refine ⟨(output.toNat + 8 * index, 8 * (remaining + 1)), by simp [regions, writes], ?_, ?_⟩
      · simpa only [ua, addressNat] using low
      · rw [ua, addressNat] at high
        omega)
  have wp : read_pc w = base + 1952#64 := by
    simp [w, storeResult, StoreKind.start, state_simp_rules]
  have w13 : r (.GPR 13#5) w = BitVec.ofNat 64 (remaining + 1) := by
    simpa [w, storeResult, storeMemory, saved, state_simp_rules] using u13
  have w16 : r (.GPR 16#5) w = BitVec.ofNat 64 (index + 1) := by
    simpa [w, storeResult, storeMemory, saved, state_simp_rules] using u16
  have wCarry : r (.FLAG .C) w =
      (AddWithCarry (BitVec.ofNat 64 carry) (right[index]?.getD 0#64) 0#1).2.c := by
    simpa [w, storeResult, storeMemory, saved, state_simp_rules] using uCarry
  have preFrame := vf.trans (uf.trans wf)
  obtain ⟨runTail, t12, t13, t14, tp⟩ := tail_run w base remaining (preFrame.code hc)
    (preFrame.error.trans he) (preFrame.aligned ha) wp w13 hr64
  have tmem := Memory.mem_eq_iff_read_mem_bytes_eq.mp (tail_memory w base)
  have stored : read_mem_bytes 8 (address output index) w =
      (LimbAdd.step 0#64 (right[index]?.getD 0#64) carry).1 := by
    simp only [w, storeResult, state_simp_rules, storeMemory, ua, StoreKind.src]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ _ _ _ physical, u15]
  refine ⟨?_, preFrame.trans (tail_frame w base regions), ?_, t13,
    t14.trans w16, tp, (tmem _ _).trans stored⟩
  · change run (readFuel right index + 2 + 8 +
        (tailOps (decide (r (.FLAG .C) w = 1#1))).length) s = tailState w base
    rw [run_plus, run_plus, run_plus, runRead, runAdd, runStore]
    exact runTail
  · change r (.GPR 12#5) (tailState w base) =
      BitVec.ofNat 64 (LimbAdd.step 0#64 (right[index]?.getD 0#64) carry).2
    simp only [t12, wCarry]
    have h := add_carry (right[index]?.getD 0#64) carry carryBound
    have cast := congrArg (BitVec.ofNat 64) h
    by_cases flag : (AddWithCarry (BitVec.ofNat 64 carry) (right[index]?.getD 0#64) 0#1).2.c = 1#1
    · simpa only [flag, ↓reduceIte, BitVec.ofNat_eq_ofNat] using cast
    · simpa only [flag, ↓reduceIte, BitVec.ofNat_eq_ofNat] using cast

end SszArm.NatAdd.SmallLoop
