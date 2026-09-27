import SszArm.NatAddLargeLoopAdds

namespace SszArm.NatAdd.LargeLoop

open SszNative
open NatCompare (saved)
open Delimited (Span Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The complete arithmetic/store/tail slice, PC1604 through the backedge or
PC2044. Its output observation is the exact native step, not merely its value. -/
theorem body_run (s : ArmState) (base left right : BitVec 64)
    (index remaining carry : Nat) (writes : List Span)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1604#64)
    (hi : index + 1 < 2^64) (hn : 0 < remaining) (hb : remaining < 2^64)
    (hcarr : carry ≤ 1)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 carry)
    (h14 : r (.GPR 14#5) s = BitVec.ofNat 64 remaining)
    (h15 : r (.GPR 15#5) s = BitVec.ofNat 64 index)
    (h16 : r (.GPR 16#5) s = left) (h17 : r (.GPR 17#5) s = right)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (storeAddress s .large).toNat + 8 ≤ 2^64)
    (apart : Protected [((storeAddress s .large).toNat, 8)]
      (r (.GPR 31#5) s - 16#64).toNat 8)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes)
    (word : ∀ a : BitVec 64,
      (storeAddress s .large).toNat ≤ a.toNat →
      a.toNat < (storeAddress s .large).toNat + 8 →
      ∃ span ∈ writes, span.1 ≤ a.toNat ∧ a.toNat < span.1 + span.2) :
    ∃ fuel t, run fuel s = t ∧ LoopFrame writes s t ∧
      read_pc t = base + (if remaining = 1 then 2044#64 else 1692#64) ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 (LimbAdd.step left right carry).2 ∧
      r (.GPR 14#5) t = BitVec.ofNat 64 (remaining - 1) ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (index + 1) ∧
      r (.GPR 13#5) t = r (.GPR 13#5) s ∧
      read_mem_bytes 8 (storeAddress s .large) t = (LimbAdd.step left right carry).1 := by
  let u := addsResult s base left right carry
  have urun : run (addsOps right carry).length s = u :=
    adds_run s base left right carry hc he ha hp h12 h16 h17
  have uf := adds_frame s base left right carry writes
  have address : storeAddress u .large = storeAddress s .large := by
    simp [u, storeAddress, StoreKind.index, addsResult, state_simp_rules]
  have up : read_pc u = base + 1628#64 := by simp [u, addsResult, state_simp_rules]
  have u16 : r (.GPR 16#5) u = (LimbAdd.step left right carry).1 := by
    simpa [u, addsResult, state_simp_rules] using add_low left right carry
  have restore := store_restore u .large (by rw [uf.sp]; exact hs)
    (by rw [address]; exact physical) (by rw [address, uf.sp]; exact apart)
  let v := storeResult u base .large
  have vrun : run 8 u = v := store_run u base .large (uf.code hc)
    (uf.error.trans he) (uf.aligned ha) up restore
  have vf := NatAdd.store_frame u base .large writes (by rw [uf.sp]; exact hs)
    (by rw [address]; exact physical) (by simpa only [uf.sp] using slot)
    (by simpa only [address] using word)
  have vp : read_pc v = base + 1660#64 := by
    simp [v, storeResult, StoreKind.start, state_simp_rules]
  have vcarry : (if r (.FLAG .C) v = 1#1 then r (.GPR 17#5) v + 1#64
      else r (.GPR 17#5) v) = BitVec.ofNat 64 (LimbAdd.step left right carry).2 := by
    have math := add_carry left right carry hcarr
    by_cases overflow : (AddWithCarry (BitVec.ofNat 64 carry + right) left 0#1).2.c = 1#1 <;>
      simpa [v, storeResult, storeMemory, saved, u, addsResult, state_simp_rules,
        carryWord, overflow] using math
  have v14 : r (.GPR 14#5) v = BitVec.ofNat 64 remaining := by
    simpa [v, storeResult, storeMemory, saved, u, addsResult, state_simp_rules] using h14
  have v15 : r (.GPR 15#5) v = BitVec.ofNat 64 index := by
    simpa [v, storeResult, storeMemory, saved, u, addsResult, state_simp_rules] using h15
  obtain ⟨trun, tf, tp, t12, t14, t15, t13, tm⟩ := tail_run v base index remaining
    (LimbAdd.step left right carry).2 ((uf.trans vf).code hc)
    ((uf.trans vf).error.trans he) ((uf.trans vf).aligned ha) vp hi hn hb v14 v15 vcarry writes
  let ops := tailOps (decide (r (.FLAG .C) v = 1#1))
  let t := block base ops v
  refine ⟨(addsOps right carry).length + 8 + ops.length, t, ?_,
    uf.trans (vf.trans tf), tp, t12, t14, t15, ?_, ?_⟩
  · rw [run_plus, run_plus, urun, vrun, trun]
  · simpa [v, storeResult, storeMemory, saved, u, addsResult, state_simp_rules] using t13
  · have readtail := (Memory.mem_eq_iff_read_mem_bytes_eq.mp tm) 8 (storeAddress s .large)
    rw [readtail]
    change read_mem_bytes 8 (storeAddress s .large) (storeResult u base .large) = _
    simp only [storeResult, state_simp_rules, storeMemory, ← address]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _
      (by rw [address]; exact physical)]
    exact u16

end SszArm.NatAdd.LargeLoop
