import SszArm.NatAddLargeLoopBodyState

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
  have uf : LoopFrame writes s u := adds_frame s base left right carry writes
  have address : storeAddress u .large = storeAddress s .large :=
    adds_address s base left right carry
  have up : read_pc u = base + 1628#64 := adds_pc s base left right carry
  have u16 : r (.GPR 16#5) u = (LimbAdd.step left right carry).1 :=
    adds_word s base left right carry
  have restore := store_restore u .large (by rw [uf.sp]; exact hs)
    (by rw [address]; exact physical) (by rw [address, uf.sp]; exact apart)
  let v := storeResult u base .large
  have vrun : run 8 u = v := store_run u base .large (uf.code hc)
    (uf.error.trans he) (uf.aligned ha) up restore
  have vf : LoopFrame writes u v := NatAdd.store_frame u base .large writes
    (by rw [uf.sp]; exact hs)
    (by rw [address]; exact physical) (by rw [uf.sp]; exact slot)
    (by simpa only [address] using word)
  have vp : read_pc v = base + 1660#64 := stored_pc u base
  have vcarry : (if r (.FLAG .C) v = 1#1 then r (.GPR 17#5) v + 1#64
      else r (.GPR 17#5) v) = BitVec.ofNat 64 (LimbAdd.step left right carry).2 :=
    stored_adds_carry s base left right carry hcarr
  have v13 : r (.GPR 13#5) v = r (.GPR 13#5) s :=
    (stored_register u base .large 13#5).trans
      (adds_register s base left right carry 13#5 (by decide) (by decide) (by decide))
  have v14 : r (.GPR 14#5) v = BitVec.ofNat 64 remaining :=
    (stored_register u base .large 14#5).trans
      ((adds_register s base left right carry 14#5 (by decide) (by decide) (by decide)).trans h14)
  have v15 : r (.GPR 15#5) v = BitVec.ofNat 64 index :=
    (stored_register u base .large 15#5).trans
      ((adds_register s base left right carry 15#5 (by decide) (by decide) (by decide)).trans h15)
  obtain ⟨trun, tf, tp, t12, t14, t15, t13, tm⟩ := tail_run v base index remaining
    (LimbAdd.step left right carry).2 ((uf.trans vf).code hc)
    ((uf.trans vf).error.trans he) ((uf.trans vf).aligned ha) vp hi hn hb v14 v15 vcarry writes
  let ops := tailOps (decide (r (.FLAG .C) v = 1#1))
  let t := block base ops v
  refine ⟨(addsOps right carry).length + 8 + ops.length, t, ?_,
    uf.trans (vf.trans tf), tp, t12, t14, t15, ?_, ?_⟩
  · rw [run_plus, run_plus, urun, vrun, trun]
  · exact t13.trans v13
  · have readtail := (Memory.mem_eq_iff_read_mem_bytes_eq.mp tm) 8 (storeAddress s .large)
    have written : read_mem_bytes 8 (storeAddress u .large) v = r (.GPR 16#5) u :=
      stored_word u base (by rw [address]; exact physical)
    rw [address] at written
    exact readtail.trans (written.trans u16)

end SszArm.NatAdd.LargeLoop
