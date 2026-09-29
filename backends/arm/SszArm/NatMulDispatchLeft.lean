import SszArm.NatMulDispatchSmallLeft

namespace SszArm.NatMul

open SszNative.Limbs

theorem left_dispatch (s : ArmState) (base : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64)
    (ho : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ LeftDispatch s t base words := by
  by_cases small : r (.GPR 1#5) s = 0#64
  · have representation := ho.small small
    rw [representation]
    exact small_left_dispatch s base hc he ha hp small
  · obtain ⟨length, source, memory⟩ := ho.large small
    have payload : r (.GPR 2#5) s = BitVec.ofNat 64 words.length := by
      rw [← length]
      arm_word_nf
    obtain ⟨fuel, u, hu, huf, count, index, raw, pc⟩ := left_large_scan s base
      (r (.GPR 1#5) s) words hc he ha hp rfl small payload source memory
    by_cases rsmall : r (.GPR 3#5) s = 0#64
    · have bound : sigWords words < 2^64 :=
        Nat.lt_of_le_of_lt (sigWords_le_length words) ho.length_bound
      have czero : (BitVec.ofNat 64 (sigWords words) = 0#64) ↔ sigWords words = 0 := by
        constructor <;> intro h <;> bv_omega
      have upc : read_pc u = base + 136#64 := by simpa only [rsmall, ↓reduceIte] using pc
      obtain ⟨rest, t, execution, frame, exitPC⟩ := small_right_route u base
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) upc
      have h4 := huf.registers 4#5 (by decide)
      refine ⟨fuel + rest, t, ?_, huf.trans frame, ?_⟩
      · rw [run_plus, hu, execution]
      · simpa only [LeftDispatch, rsmall, ↓reduceIte, index, czero, h4] using exitPC
    · refine ⟨fuel, u, hu, huf, ?_⟩
      simpa [LeftDispatch, rsmall] using And.intro count (And.intro raw pc)

end SszArm.NatMul
